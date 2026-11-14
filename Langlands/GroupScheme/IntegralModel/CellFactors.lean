import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication

/-! # Extracting integral generic factors from actual cell coordinates -/

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
    {G U P : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel A K G) (MU : IntegralModel A K U) (MP : IntegralModel A K P)
    {i : U ⟶ G} {p : P ⟶ G}
    (φ : MU.Hom M i) (ψ : MP.Hom M p)

/-- The two original integral sections of an integral cell coordinate. -/
def cellFactorSections
    (a : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ MU.group.X ⊗ MP.group.X) :
    MU.integralSections × MP.integralSections :=
  (a ≫ fst MU.group.X MP.group.X, a ≫ snd MU.group.X MP.group.X)

/-- The product of the two extracted integral sections is the original
integral multiplication of the cell coordinate. -/
theorem cellFactorSections_product
    (a : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ MU.group.X ⊗ MP.group.X) :
    rationalPoints.map φ.hom (cellFactorSections MU MP a).1 *
        rationalPoints.map ψ.hom (cellFactorSections MU MP a).2 =
      a ≫ SubgroupFunctor.cellMultiplication φ.hom ψ.hom := by
  simp only [cellFactorSections, SubgroupFunctor.cellMultiplication, MonObj.comp_mul]
  rfl

variable [Mono (SubgroupFunctor.cellMultiplication i p)]

/-- Monicity of the generic multiplication identifies both generic factors
with the images of the original integral coordinate sections. -/
theorem cellFactorSections_generic_eq (x : M.integralSections)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ MU.group.X ⊗ MP.group.X)
    (ha : a ≫ SubgroupFunctor.cellMultiplication φ.hom ψ.hom = x)
    (u : rationalPoints U) (v : rationalPoints P)
    (huv : rationalPoints.map i u * rationalPoints.map p v = M.integralPointMap x) :
    MU.integralPointMap (cellFactorSections MU MP a).1 = u ∧
      MP.integralPointMap (cellFactorSections MU MP a).2 = v := by
  have hproduct :
      rationalPoints.map i (MU.integralPointMap (cellFactorSections MU MP a).1) *
          rationalPoints.map p (MP.integralPointMap (cellFactorSections MU MP a).2) =
        M.integralPointMap x := by
    rw [← φ.integralPointMap_naturality, ← ψ.integralPointMap_naturality,
      ← map_mul, cellFactorSections_product, ha]
  have hcoordinates :
      lift (MU.integralPointMap (cellFactorSections MU MP a).1)
          (MP.integralPointMap (cellFactorSections MU MP a).2) = lift u v := by
    apply (cancel_mono (SubgroupFunctor.cellMultiplication i p)).mp
    rw [SubgroupFunctor.lift_cellMultiplication, SubgroupFunctor.lift_cellMultiplication]
    exact hproduct.trans huv.symm
  constructor
  · have h := congrArg (fun f => f ≫ fst U.X P.X) hcoordinates
    simpa only [lift_fst] using h
  · have h := congrArg (fun f => f ≫ snd U.X P.X) hcoordinates
    simpa only [lift_snd] using h

/-- Integral cell coordinates force any prescribed generic factorization
through a monic generic cell to have integral factors. -/
theorem integral_factors_of_cell_lift (x : M.integralSections)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ MU.group.X ⊗ MP.group.X)
    (ha : a ≫ SubgroupFunctor.cellMultiplication φ.hom ψ.hom = x)
    (u : rationalPoints U) (v : rationalPoints P)
    (huv : rationalPoints.map i u * rationalPoints.map p v = M.integralPointMap x) :
    u ∈ MU.integralPoints ∧ v ∈ MP.integralPoints := by
  obtain ⟨hu, hv⟩ := cellFactorSections_generic_eq M MU MP φ ψ x a ha u v huv
  exact ⟨⟨(cellFactorSections MU MP a).1, hu⟩,
    ⟨(cellFactorSections MU MP a).2, hv⟩⟩

end Langlands.GroupScheme.IntegralModel
