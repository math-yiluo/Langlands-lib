import Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication

/-! # Ambient integrality from an integral cell coordinate -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {A K : Type u} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel A K G)
    {U P : GroupScheme (Spec (CommRingCat.of A))}
    (i : U ⟶ M.group) (p : P ⟶ M.group)

/-- Project an integral binary cell coordinate and send both factors to the
original ambient integral model. -/
def ambientCellFactorSections
    (a : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X) :
    M.integralSections × M.integralSections :=
  (rationalPoints.map i (a ≫ fst U.X P.X),
    rationalPoints.map p (a ≫ snd U.X P.X))

variable [Mono (SubgroupFunctor.cellMultiplication (M.genericHom i) (M.genericHom p))]

/-- A prescribed generic binary factorization through the actual generic
factor inclusions is identified with the images of the original integral
coordinate sections. No integral models of the two factors are required. -/
theorem ambient_cell_factors_eq (x : M.integralSections)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X)
    (ha : a ≫ SubgroupFunctor.cellMultiplication i p = x)
    (u v : rationalPoints G)
    (hu : u ∈ (rationalPoints.map (M.genericHom i)).range)
    (hv : v ∈ (rationalPoints.map (M.genericHom p)).range)
    (huv : u * v = M.integralPointMap x) :
    M.integralPointMap (M.ambientCellFactorSections i p a).1 = u ∧
      M.integralPointMap (M.ambientCellFactorSections i p a).2 = v := by
  obtain ⟨u₀, rfl⟩ := hu
  obtain ⟨v₀, rfl⟩ := hv
  let uA : rationalPoints U := a ≫ fst U.X P.X
  let vA : rationalPoints P := a ≫ snd U.X P.X
  have hA : rationalPoints.map i uA * rationalPoints.map p vA = x := by
    rw [← ha]
    simp only [uA, vA, SubgroupFunctor.cellMultiplication, MonObj.comp_mul]
    rfl
  have hproduct :
      rationalPoints.map (M.genericHom i)
          (baseChangeSectionHom (Spec.algebraMap A K) U uA) *
        rationalPoints.map (M.genericHom p)
          (baseChangeSectionHom (Spec.algebraMap A K) P vA) =
      rationalPoints.map (M.genericHom i) u₀ * rationalPoints.map (M.genericHom p) v₀ := by
    rw [← M.subgroupPointMap_apply i, ← M.subgroupPointMap_apply p]
    change M.integralPointMap (rationalPoints.map i uA) *
      M.integralPointMap (rationalPoints.map p vA) = _
    rw [← map_mul, hA, huv]
  have hc :
      lift (baseChangeSectionHom (Spec.algebraMap A K) U uA)
          (baseChangeSectionHom (Spec.algebraMap A K) P vA) = lift u₀ v₀ := by
    apply (cancel_mono (SubgroupFunctor.cellMultiplication
      (M.genericHom i) (M.genericHom p))).mp
    rw [SubgroupFunctor.lift_cellMultiplication, SubgroupFunctor.lift_cellMultiplication]
    exact hproduct
  have hu₀ : baseChangeSectionHom (Spec.algebraMap A K) U uA = u₀ := by
    simpa only [lift_fst] using congrArg (fun f => f ≫ fst _ _) hc
  have hv₀ : baseChangeSectionHom (Spec.algebraMap A K) P vA = v₀ := by
    simpa only [lift_snd] using congrArg (fun f => f ≫ snd _ _) hc
  constructor
  · change M.subgroupPointMap i uA = _
    rw [M.subgroupPointMap_apply, hu₀]
  · change M.subgroupPointMap p vA = _
    rw [M.subgroupPointMap_apply, hv₀]

/-- Actual integral cell coordinates and monicity of the generic cell force
both prescribed ambient factors to belong to the original integral subgroup. -/
theorem ambient_integral_factors_of_cell_lift (x : M.integralSections)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X)
    (ha : a ≫ SubgroupFunctor.cellMultiplication i p = x)
    (u v : rationalPoints G)
    (hu : u ∈ (rationalPoints.map (M.genericHom i)).range)
    (hv : v ∈ (rationalPoints.map (M.genericHom p)).range)
    (huv : u * v = M.integralPointMap x) :
    u ∈ M.integralPoints ∧ v ∈ M.integralPoints := by
  obtain ⟨hu', hv'⟩ := M.ambient_cell_factors_eq i p x a ha u v hu hv huv
  exact ⟨⟨(M.ambientCellFactorSections i p a).1, hu'⟩,
    ⟨(M.ambientCellFactorSections i p a).2, hv'⟩⟩

end Langlands.GroupScheme.IntegralModel
