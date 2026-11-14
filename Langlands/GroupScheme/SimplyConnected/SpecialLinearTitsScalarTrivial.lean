import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsOuterDiscrepancy

/-! # Scalar inner representatives give trivial discrepancies -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix
open Langlands.LinearAlgebra.SpecialLinearHermitianNormalization

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K L))

/-- A scalar inner representative gives the identity discrepancy on every test. -/
theorem HasInnerDiscrepancy.discrepancy_eq_self_of_scalar {σ : L ≃ₐ[K] L} {c : Lˣ}
    (hX : HasInnerDiscrepancy E σ (GeneralLinearGroup.scalar (Fin (n + 1)) c))
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy E σ a g = g := by
  apply SpecialLinearGroup.toGL_injective
  rw [hX Z a g]
  simpa only [mul_one, map_one, inv_one, one_mul] using
    map_scalar_mul_conjugate (coefficients a) c 1 (SpecialLinearGroup.toGL g)

/-- If every inner representative over `H` becomes scalar after the coboundary change by `P`,
then the presentation changed by `P` has trivial discrepancy on `H`. -/
theorem hasTrivialDiscrepancy_coordinateChange_of_scalar
    {H : Subgroup (L ≃ₐ[K] L)} {x : (L ≃ₐ[K] L) → GeneralLinearGroup (Fin (n + 1)) L}
    (hx : ∀ σ ∈ H, HasInnerDiscrepancy E σ (x σ))
    (P : GeneralLinearGroup (Fin (n + 1)) L)
    (hs : ∀ σ ∈ H, ∃ c : Lˣ,
      P⁻¹ * x σ * GeneralLinearGroup.map σ.toRingHom P =
        GeneralLinearGroup.scalar (Fin (n + 1)) c) :
    HasTrivialDiscrepancy (coordinateChange E P) H := by
  intro σ Z a g
  obtain ⟨c, hc⟩ := hs σ.val σ.property
  have h := (hx σ.val σ.property).coordinateChange E P
  rw [hc] at h
  exact h.discrepancy_eq_self_of_scalar (coordinateChange E P) a g

end Langlands.GroupScheme.SpecialLinearTitsCocycle
