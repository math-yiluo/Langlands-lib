import Langlands.Representation.Geometric.RefinementSolomonCoefficients

/-! Regrouping actual source-refinement sums in an arbitrary abelian group. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe uF uM

variable {n : ℕ} {M : Type uM} [AddCommGroup M]

/-- The ambient signed sum of values indexed by the source refinement of each
minimal representative. -/
def refinementSignedSum (B : BlockShape n)
    (S : ∀ C : BlockShape n, MinimalRepresentatives B C → BlockRefinement B)
    (f : BlockRefinement B → M) : M := by
  let _ : Fintype (BlockShape n) := Fintype.ofFinite _
  let _ (C : BlockShape n) : Fintype (MinimalRepresentatives B C) := Fintype.ofFinite _
  exact ∑ C : BlockShape n, (-1 : ℤ) ^ (n - C.length) •
    ∑ w : MinimalRepresentatives B C, f (S C w)

private theorem sum_comp_eq_fiber_count {α β : Type*} [Fintype α] [Fintype β]
    (s : α → β) (f : β → M) :
    ∑ a, f (s a) = ∑ b, (Nat.card {a // s a = b} : ℤ) • f b := by
  classical
  rw [← Fintype.sum_fiberwise' s f]
  exact Finset.sum_congr rfl fun b _ => by simp [Nat.card_eq_fintype_card]

/-- Regrouping by the source refinement gives its signed fiber coefficient. -/
theorem refinementSignedSum_eq_sum_coefficients (B : BlockShape n)
    (S : ∀ C : BlockShape n, MinimalRepresentatives B C → BlockRefinement B)
    (f : BlockRefinement B → M) [Fintype (BlockRefinement B)] :
    refinementSignedSum B S f =
      ∑ Q : BlockRefinement B, refinementSolomonCoefficient B S Q • f Q := by
  classical
  let _ : Fintype (BlockShape n) := Fintype.ofFinite _
  let _ (C : BlockShape n) : Fintype (MinimalRepresentatives B C) := Fintype.ofFinite _
  unfold refinementSignedSum
  simp_rw [sum_comp_eq_fiber_count, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ => ?_
  simp only [refinementSolomonCoefficient, Finset.sum_smul]

/-- Actual source intersections turn the ambient signed sum into the intrinsic
product-Levi signed sum, including in rank zero. -/
theorem refinementSignedSum_eq_refinement_sum
    (F : Type uF) [CommRing F] [Nontrivial F] (B : BlockShape n)
    (S : ∀ C : BlockShape n, MinimalRepresentatives B C → BlockRefinement B)
    (hS : ∀ C w, sourceLevi F B C w.val = refinedLevi F B (S C w))
    (f : BlockRefinement B → M) [Fintype (BlockRefinement B)] :
    refinementSignedSum B S f =
      ∑ Q : BlockRefinement B, (-1 : ℤ) ^ Aubert.refinementSignExponent B Q • f Q := by
  rw [refinementSignedSum_eq_sum_coefficients]
  exact Finset.sum_congr rfl fun Q _ => by
    rw [refinementSolomonCoefficient_eq F B S hS Q]

end Langlands.Geometric
