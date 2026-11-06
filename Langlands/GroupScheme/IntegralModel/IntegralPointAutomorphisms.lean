import Langlands.GroupScheme.IntegralModel.IntegralPointDescent

/-! # Coefficient automorphisms on the extended original integral image -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology
open GaloisPointComparison

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

/-- A coefficient automorphism preserving the extended coefficient ring preserves
and reflects the actual extended original-model integral image. -/
theorem mem_baseChange_coefficientIntegralPoints_conjugate_iff
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ x : L,
      σ x ∈ Set.range (algebraMap A L) ↔ x ∈ Set.range (algebraMap A L))
    (p : G.affinePoints (CommAlgCat.of K L)) :
    GaloisPoint.conjugate K L G σ p ∈
        (M.baseChange A L).coefficientIntegralPoints K L ↔
      p ∈ (M.baseChange A L).coefficientIntegralPoints K L := by
  rw [M.mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates A L,
    M.mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates A L]
  apply forall_congr'
  intro a
  change G.affinePointEvaluation (CommAlgCat.of K L)
    (G.affinePointMap (CommAlgCat.ofHom σ.toAlgHom) p)
      (M.genericCoordinate a) ∈ Set.range (algebraMap A L) ↔ _
  rw [G.affinePointEvaluation_map]
  exact hσ _

/-- The same preservation and reflection on the existing rational-point carrier,
using its already defined coefficient conjugation. -/
theorem mem_baseChange_integralPoints_rationalConjugate_iff
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ x : L,
      σ x ∈ Set.range (algebraMap A L) ↔ x ∈ Set.range (algebraMap A L))
    (g : rationalPoints (baseChanged K L G)) :
    rationalConjugate K L G σ g ∈ (M.baseChange A L).integralPoints ↔
      g ∈ (M.baseChange A L).integralPoints := by
  have h := M.mem_baseChange_coefficientIntegralPoints_conjugate_iff A L σ hσ
    (baseChangeCoeffEquiv K L G g)
  rw [← baseChangeCoeffEquiv_rationalConjugate,
    (M.baseChange A L).mem_coefficientIntegralPoints_iff,
    (M.baseChange A L).mem_coefficientIntegralPoints_iff,
    MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h
  exact h

/-- Restrict the existing rational conjugation to an actual multiplicative
automorphism of the extended original-model integral subgroup. -/
def baseChangeIntegralPointAut
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ x : L,
      σ x ∈ Set.range (algebraMap A L) ↔ x ∈ Set.range (algebraMap A L)) :
    MulAut (M.baseChange A L).integralPoints where
  toFun g := ⟨rationalConjugate K L G σ g.val,
    (M.mem_baseChange_integralPoints_rationalConjugate_iff A L σ hσ g.val).mpr
      g.property⟩
  invFun g := ⟨(rationalConjugate K L G σ).symm g.val, by
    apply (M.mem_baseChange_integralPoints_rationalConjugate_iff A L σ hσ _).mp
    simpa only [MulEquiv.apply_symm_apply] using g.property⟩
  left_inv g := Subtype.ext ((rationalConjugate K L G σ).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((rationalConjugate K L G σ).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext ((rationalConjugate K L G σ).map_mul g.val h.val)

@[simp] theorem baseChangeIntegralPointAut_coe
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ x : L,
      σ x ∈ Set.range (algebraMap A L) ↔ x ∈ Set.range (algebraMap A L))
    (g : (M.baseChange A L).integralPoints) :
    (M.baseChangeIntegralPointAut A L σ hσ g : rationalPoints (baseChanged K L G)) =
      rationalConjugate K L G σ g := rfl

end Langlands.GroupScheme.IntegralModel
