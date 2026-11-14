import Langlands.GroupScheme.UnramifiedIntegralTwoFactorDescent

/-! # Rational-point forms of smooth intersection-model factor descent -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.LocalGalois.Separable

namespace Langlands.GroupScheme.IntegralModel

open GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {U G : GroupScheme (Spec (CommRingCat.of F))}

/-- The intersection-model comparison on rational points of the actual
maximal-unramified base change. -/
def IsRationalIntersectionModel (M : IntegralModel 𝒪[F] F U) (q : U ⟶ G)
    (A B : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G))) : Prop :=
  ∀ z : rationalPoints (baseChanged F (inertiaFixedField F) U),
    M.HasIntegralCoordinates (inertiaFixedField F)
      (baseChangeCoeffEquiv F (inertiaFixedField F) U z) ↔
    rationalPoints.map
      ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map q) z ∈ A ⊓ B

/-- The two intersection comparisons are equivalent under the published
multiplicative base-change point comparison. -/
theorem isRationalIntersectionModel_iff (M : IntegralModel 𝒪[F] F U) (q : U ⟶ G)
    (A B : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G))) :
    M.IsRationalIntersectionModel q A B ↔
      M.IsIntersectionModel q
        (A.map (baseChangeCoeffEquiv F (inertiaFixedField F) G).toMonoidHom)
        (B.map (baseChangeCoeffEquiv F (inertiaFixedField F) G).toMonoidHom) := by
  let eU := baseChangeCoeffEquiv F (inertiaFixedField F) U
  constructor
  · intro h z
    obtain ⟨w, rfl⟩ := eU.surjective z
    have hw := h w
    simpa only [eU, ← baseChangeCoeffEquiv_map, Subgroup.mem_inf,
      Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using hw
  · intro h z
    have hz := h (eU z)
    simpa only [eU, ← baseChangeCoeffEquiv_map, Subgroup.mem_inf,
      Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using hz

/-- Descend a first factor through the model while preserving both
rational-point subgroup bounds. -/
theorem exists_rational_factorization_of_rationalIntersectionModel
    [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
    (M : IntegralModel 𝒪[F] F U) (hM : M.IsSmooth)
    (hconn : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left)
    (q : U ⟶ G)
    (A B : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)))
    (hmodel : M.IsRationalIntersectionModel q A B)
    (hA : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) x,
      x ∈ A → rationalConjugate F (inertiaFixedField F) G σ x ∈ A)
    (hB : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) x,
      x ∈ B → rationalConjugate F (inertiaFixedField F) G σ x ∈ B)
    (g : rationalPoints G)
    (x : rationalPoints (baseChanged F (inertiaFixedField F) U))
    (y : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hx : rationalPoints.map
      ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map q) x ∈ A)
    (hy : y ∈ B)
    (hxy : rationalExtend F (inertiaFixedField F) G g =
      rationalPoints.map
        ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map q) x * y) :
    ∃ (u : rationalPoints U) (v : rationalPoints G),
      g = rationalPoints.map q u * v ∧
      rationalExtend F (inertiaFixedField F) G (rationalPoints.map q u) ∈ A ∧
      rationalExtend F (inertiaFixedField F) G v ∈ B := by
  let eU := baseChangeCoeffEquiv F (inertiaFixedField F) U
  let eG := baseChangeCoeffEquiv F (inertiaFixedField F) G
  let A' := A.map eG.toMonoidHom
  let B' := B.map eG.toMonoidHom
  have hstable (C : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)))
      (hC : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) z,
        z ∈ C → rationalConjugate F (inertiaFixedField F) G σ z ∈ C) :
      ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) z,
        z ∈ C.map eG.toMonoidHom →
          GaloisPoint.conjugate F (inertiaFixedField F) G σ z ∈
            C.map eG.toMonoidHom := by
    intro σ z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_map.mpr
      ⟨rationalConjugate F (inertiaFixedField F) G σ w, hC σ w hw,
        baseChangeCoeffEquiv_rationalConjugate F (inertiaFixedField F) G σ w⟩
  have hx' : U.affinePointsTarget q (CommAlgCat.of F (inertiaFixedField F)) (eU x) ∈ A' := by
    rw [← baseChangeCoeffEquiv_map]
    exact Subgroup.mem_map.mpr ⟨_, hx, rfl⟩
  have hy' : eG y ∈ B' := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have hxy' := congrArg eG hxy
  rw [baseChangeCoeffEquiv_rationalExtend, map_mul, baseChangeCoeffEquiv_map] at hxy'
  obtain ⟨u, v, hg, hu, hv⟩ :=
    M.exists_rational_factorization_of_intersectionModel hM hconn q A' B'
      ((M.isRationalIntersectionModel_iff q A B).mp hmodel)
      (hstable A hA) (hstable B hB) g (eU x) (eG y) hx' hy' hxy'
  refine ⟨u, v, hg, ?_, ?_⟩
  · exact (Subgroup.mem_map_iff_mem (f := eG.toMonoidHom) eG.injective).mp
      (show eG (rationalExtend F (inertiaFixedField F) G
        (rationalPoints.map q u)) ∈ A' from by
          simpa only [eG, baseChangeCoeffEquiv_rationalExtend] using hu)
  · exact (Subgroup.mem_map_iff_mem (f := eG.toMonoidHom) eG.injective).mp
      (show eG (rationalExtend F (inertiaFixedField F) G v) ∈ B' from by
          simpa only [eG, baseChangeCoeffEquiv_rationalExtend] using hv)

/-- The modeled factor can occur on the right: apply first-factor descent
to the inverse product and invert the resulting rational factors. -/
theorem exists_rational_right_factorization_of_rationalIntersectionModel
    [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
    (M : IntegralModel 𝒪[F] F U) (hM : M.IsSmooth)
    (hconn : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left)
    (q : U ⟶ G)
    (A B : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)))
    (hmodel : M.IsRationalIntersectionModel q A B)
    (hA : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) x,
      x ∈ A → rationalConjugate F (inertiaFixedField F) G σ x ∈ A)
    (hB : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) x,
      x ∈ B → rationalConjugate F (inertiaFixedField F) G σ x ∈ B)
    (g : rationalPoints G)
    (x : rationalPoints (baseChanged F (inertiaFixedField F) U))
    (y : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hx : rationalPoints.map
      ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map q) x ∈ A)
    (hy : y ∈ B)
    (hxy : rationalExtend F (inertiaFixedField F) G g =
      y * rationalPoints.map
        ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map q) x) :
    ∃ (v : rationalPoints G) (u : rationalPoints U),
      g = v * rationalPoints.map q u ∧
      rationalExtend F (inertiaFixedField F) G v ∈ B ∧
      rationalExtend F (inertiaFixedField F) G (rationalPoints.map q u) ∈ A := by
  have hxy' : rationalExtend F (inertiaFixedField F) G g⁻¹ =
      rationalPoints.map
        ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map q) x⁻¹ * y⁻¹ := by
    rw [map_inv, hxy, mul_inv_rev, map_inv]
  obtain ⟨u, v, hg, hu, hv⟩ :=
    M.exists_rational_factorization_of_rationalIntersectionModel hM hconn q A B hmodel
      hA hB g⁻¹ x⁻¹ y⁻¹ (by simpa only [map_inv] using A.inv_mem hx) (B.inv_mem hy) hxy'
  refine ⟨v⁻¹, u⁻¹, ?_, ?_, ?_⟩
  · have hi := congrArg Inv.inv hg
    simpa only [inv_inv, mul_inv_rev, ← map_inv] using hi
  · simpa only [map_inv] using B.inv_mem hv
  · simpa only [map_inv] using A.inv_mem hu

end Langlands.GroupScheme.IntegralModel
