import Langlands.AlgebraicGeometry.ProjectiveSpace.PointLines
import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearAction

/-! # Compatibility of actual rational points with the linear action -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable {K : Type u} [Field K] (n : ℕ)

/-- The linear action permutes actual rational-point morphisms over the field. -/
def linearActionPointEquiv
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n //
      p ≫ projectiveSpaceToSpec K n = 𝟙 _} ≃
    {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n //
      p ≫ projectiveSpaceToSpec K n = 𝟙 _} where
  toFun p := ⟨p.1 ≫ linearAction K n e, by
    rw [Category.assoc, linearAction_comp_toSpec, p.2]⟩
  invFun p := ⟨p.1 ≫ linearAction K n e.symm, by
    rw [Category.assoc, linearAction_comp_toSpec, p.2]⟩
  left_inv p := Subtype.ext (by
    dsimp
    rw [Category.assoc, linearAction_comp, LinearEquiv.self_trans_symm, linearAction_refl,
      Category.comp_id])
  right_inv p := Subtype.ext (by
    dsimp
    rw [Category.assoc, linearAction_comp, LinearEquiv.symm_trans_self, linearAction_refl,
      Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Linear vanishing on the chosen image representative is vanishing after the linear map. -/
theorem linear_vanishing_map_iff
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (v : ℙ K (Fin (n + 1) → K)) (ℓ : (Fin (n + 1) → K) →ₗ[K] K) :
    ℓ (Projectivization.map e.toLinearMap e.injective v).rep = 0 ↔
      (ℓ.comp e.toLinearMap) v.rep = 0 := by
  have hne : e v.rep ≠ 0 := by
    intro h
    exact Projectivization.rep_nonzero v (e.injective (by simpa using h))
  have heq : Projectivization.map e.toLinearMap e.injective v =
      Projectivization.mk K (e v.rep) hne := by
    simpa only [Projectivization.mk_rep, LinearEquiv.coe_coe] using
      Projectivization.map_mk e.toLinearMap e.injective v.rep (Projectivization.rep_nonzero v)
  rw [heq]
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K (e v.rep) hne
  rw [← ha, Units.smul_def, map_smul]
  simp

/-- Actual scheme action and linear action on coordinate lines agree. -/
theorem pointLine_linearAction
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _)
    (hp' : (p ≫ linearAction K n e) ≫ projectiveSpaceToSpec K n = 𝟙 _) :
    pointLine n (p ≫ linearAction K n e) hp' =
      Projectivization.map e.toLinearMap e.injective (pointLine n p hp) := by
  apply projectiveLine_eq_of_linear_vanishing n
  intro ℓ
  rw [← pointLine_linearForm_mem_iff n (p ≫ linearAction K n e) hp' ℓ]
  change (linearFormPolynomialEquiv K n ℓ : ProjectiveCoordinateRing K n) ∈
      (linearAction K n e (p (IsLocalRing.closedPoint K))).asHomogeneousIdeal ↔ _
  rw [linearAction_linearForm_mem_iff, pointLine_linearForm_mem_iff]
  exact (linear_vanishing_map_iff n e (pointLine n p hp) ℓ).symm

/-- The injective rational-point comparison intertwines the two actions. -/
theorem pointLineEmbedding_linearActionPointEquiv
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (p : {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n //
      p ≫ projectiveSpaceToSpec K n = 𝟙 _}) :
    pointLineEmbedding n (linearActionPointEquiv n e p) =
      Projectivization.map e.toLinearMap e.injective (pointLineEmbedding n p) := by
  exact pointLine_linearAction n e p.1 p.2 _

end Langlands.AlgebraicGeometry.ProjectiveSpace
