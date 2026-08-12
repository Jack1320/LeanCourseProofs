import Mathlib

def converges_to (a : ℕ → ℝ ) (L : ℝ ) : Prop :=
  ∀ ε > 0, ∃ N , ∀ n, n ≥ N → |a n - L| < ε

theorem limit_unique (a : ℕ → ℝ ) (L M : ℝ )
  (hL : converges_to a L) (hM : converges_to a M) : L = M := by
    suffices h : ∀ ε > 0, |L - M| < ε by
      exact eq_of_abs_sub_nonpos (le_of_forall_pos_lt_add (fun ε hε => by linarith [h ε hε ]))
    
    unfold converges_to at hL hM
    intro ε hε
    obtain ⟨ N₁, hN₁⟩ := hL (ε/2) (by linarith)
    obtain ⟨ N₂, hN₂⟩ := hM (ε / 2) (by linarith)

    let N:= max N₁ N₂ 
    have h₁ := hN₁ N (le_max_left N₁ N₂)
    have h₂ := hN₂ N (le_max_right N₁ N₂ )
    have h₃ : |a N - L| + |a N - M| < ε := by linarith
    have h₄ : |L-M| ≤ |L - a N| + |a N - M| := by
      calc |L - M| = |(L - a N) + (a N - M)| := by ring_nf
      _ ≤ |L - a N| + |a N - M| := by exact abs_add_le _ _
    rw [abs_sub_comm L (a N)] at h₄
    linarith
