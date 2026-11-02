import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # Direct-sum decompositions from finitely supported coefficient maps -/

noncomputable section

open DirectSum

namespace Langlands.LinearAlgebra

variable {R V ι : Type*} [Semiring R] [AddCommMonoid V] [Module R V] [DecidableEq ι]
  (W : ι → Submodule R V) (p : V →ₗ[R] (ι →₀ V))

/-- If `p` sends an element of `W i` to the coefficient family concentrated at `i`, then the
`i`-th coefficient of `p` applied to the sum of a family `x ∈ ⨁ i, W i` is `x i`. -/
theorem finsuppCoeff_coeAddMonoidHom
    (hdiag : ∀ (i : ι) (v : W i), p (v : V) = Finsupp.single i (v : V))
    (x : ⨁ i, W i) (i : ι) :
    p (DirectSum.coeAddMonoidHom W x) i = (x i : V) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j w =>
    rw [coeAddMonoidHom_of, hdiag j w, coe_of_apply, Finsupp.single_apply]
    split_ifs <;> simp
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply, hx, hy, DirectSum.add_apply, Submodule.coe_add]

/-- The decomposition `V = ⨁ i, W i` attached to a coefficient map `p : V → (ι →₀ V)` whose
coefficients lie in the `W i` (`hmem`), which is the identity on each `W i` (`hdiag`), and whose
coefficients sum back to the original element (`hsum`). An element `v` is sent to the family
`i ↦ p v i`. -/
@[instance_reducible]
def finsuppDecomposition (hmem : ∀ (v : V) (i : ι), p v i ∈ W i)
    (hdiag : ∀ (i : ι) (v : W i), p (v : V) = Finsupp.single i (v : V))
    (hsum : ∀ v : V, (p v).sum (fun _ x => x) = v) : Decomposition W :=
  have hleft : ∀ v : V, DirectSum.coeAddMonoidHom W
      (∑ i ∈ (p v).support, DirectSum.of (fun i => W i) i ⟨p v i, hmem v i⟩) = v := by
    intro v
    rw [map_sum]
    simp only [coeAddMonoidHom_of]
    exact hsum v
  { decompose' := fun v =>
      ∑ i ∈ (p v).support, DirectSum.of (fun i => W i) i ⟨p v i, hmem v i⟩
    left_inv := hleft
    right_inv := by
      intro x
      apply DirectSum.ext
      intro i
      apply Subtype.ext
      rw [← finsuppCoeff_coeAddMonoidHom W p hdiag, hleft,
        finsuppCoeff_coeAddMonoidHom W p hdiag] }

/-- The component of `v` in `W i` for `finsuppDecomposition` is the coefficient `p v i`. -/
theorem coe_finsuppDecomposition_decompose'_apply (hmem : ∀ (v : V) (i : ι), p v i ∈ W i)
    (hdiag : ∀ (i : ι) (v : W i), p (v : V) = Finsupp.single i (v : V))
    (hsum : ∀ v : V, (p v).sum (fun _ x => x) = v) (v : V) (i : ι) :
    ((finsuppDecomposition W p hmem hdiag hsum).decompose' v i : V) = p v i := by
  rw [← finsuppCoeff_coeAddMonoidHom W p hdiag,
    (finsuppDecomposition W p hmem hdiag hsum).left_inv v]

/-- **Direct sum from coefficients.** If a linear map `p : V → (ι →₀ V)` has its `i`-th
coefficients in `W i`, restricts on each `W i` to `v ↦ Finsupp.single i v`, and its coefficients
sum back to the original element, then `V` is the internal direct sum of the `W i`. -/
theorem isInternal_of_finsupp (hmem : ∀ (v : V) (i : ι), p v i ∈ W i)
    (hdiag : ∀ (i : ι) (v : W i), p (v : V) = Finsupp.single i (v : V))
    (hsum : ∀ v : V, (p v).sum (fun _ x => x) = v) : DirectSum.IsInternal W :=
  letI := finsuppDecomposition W p hmem hdiag hsum
  Decomposition.isInternal W

end Langlands.LinearAlgebra
