import Langlands.GroupScheme.IntegralModel.DynamicCellFactors
import Langlands.GroupScheme.Rational.PrescribedOppositeCell

/-! # Integral prescribed opposite factors from translated cell coordinates -/

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
    (M : IntegralModel A K G) [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of K))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (hroot : HasRelativeRootSystem i)
    (a : characterLattice T) (ha : a ∈ relativeRoots i)
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν)
    (χ : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ M.group)
    (hχ : Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ ≫
      M.genericIso.hom = CommGroupScheme.groupHom ν ≫ i)
    {U P : GroupScheme (Spec (CommRingCat.of A))}
    (j : U ⟶ M.group) (r : P ⟶ M.group)
    (hj : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy j)
    (hr : (Dynamic.parabolic χ).IsRepresentedBy r)
    (m : M.integralSections) (n : normalizerPoints i)
    (hm : M.integralPointMap m = n.val)
    (hn : IsRelativeReflection i a (QuotientGroup.mk n))

include hT hroot ha hpos hχ hj hr hm hn

/-- A translated integral cell identifies the inverse of the prescribed first
opposite factor with an integral dynamic coordinate. -/
theorem integral_first_oppositeFactor_of_cell_lift
    (x : M.integralSections)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)))
    (hx1 : M.integralPointMap x ≠ 1)
    (p : rationalPoints G × rationalPoints G)
    (hp : RelativeRoot.IsOppositeFactorPair i a (M.integralPointMap x) p)
    (c : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X)
    (hc : c ≫ SubgroupFunctor.cellMultiplication j r = x * m⁻¹) :
    p.1 ∈ M.integralPoints := by
  let q := hp.translatedCellFactorPair i hT hroot ha hx hx1 n hn ν hpos
  have hu : q.val.1 ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ ≫
        M.genericIso.hom))).carrier (Over.mk (𝟙 _)) := by
    rw [hχ]
    exact q.property.1
  have hv : q.val.2 ∈ (Dynamic.parabolic
      (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ ≫
        M.genericIso.hom)).carrier (Over.mk (𝟙 _)) := by
    rw [hχ]
    exact q.property.2.1
  have hprod : q.val.1 * q.val.2 = M.integralPointMap (x * m⁻¹) := by
    rw [map_mul, map_inv, hm]
    exact q.property.2.2.symm
  have h := M.integral_dynamic_factors_of_cell_lift χ j r hj hr
    (x * m⁻¹) c hc q.val.1 q.val.2 hu hv hprod
  have hinv : p.1⁻¹ ∈ M.integralPoints := h.1
  simpa only [inv_inv] using Subgroup.inv_mem M.integralPoints hinv

/-- Integral translated cells for a point and its inverse imply integrality
of both members of its prescribed normalizing opposite pair. -/
theorem integral_oppositeFactors_of_cell_lifts
    (x : M.integralSections)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)))
    (hx1 : M.integralPointMap x ≠ 1)
    (p : rationalPoints G × rationalPoints G)
    (hp : RelativeRoot.IsOppositeFactorPair i a (M.integralPointMap x) p)
    (c d : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X)
    (hc : c ≫ SubgroupFunctor.cellMultiplication j r = x * m⁻¹)
    (hd : d ≫ SubgroupFunctor.cellMultiplication j r = x⁻¹ * m⁻¹) :
    p.1 ∈ M.integralPoints ∧ p.2 ∈ M.integralPoints := by
  refine ⟨M.integral_first_oppositeFactor_of_cell_lift i hT hroot a ha ν hpos χ hχ
    j r hj hr m n hm hn x hx hx1 p hp c hc, ?_⟩
  have hxinv : M.integralPointMap x⁻¹ ∈
      (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  have hxinv1 : M.integralPointMap x⁻¹ ≠ 1 := by
    rw [map_inv]
    exact inv_ne_one.mpr hx1
  have hpinv : RelativeRoot.IsOppositeFactorPair i a (M.integralPointMap x⁻¹)
      (p.2⁻¹, p.1⁻¹) := by
    refine ⟨Subgroup.inv_mem _ hp.2.1, Subgroup.inv_mem _ hp.1, ?_⟩
    change p.2⁻¹ * M.integralPointMap x⁻¹ * p.1⁻¹ ∈ normalizerPoints i
    rw [map_inv]
    have heq : p.2⁻¹ * (M.integralPointMap x)⁻¹ * p.1⁻¹ =
        (p.1 * M.integralPointMap x * p.2)⁻¹ := by group
    rw [heq]
    exact Subgroup.inv_mem _ hp.2.2
  have hinv := M.integral_first_oppositeFactor_of_cell_lift i hT hroot a ha ν hpos
    χ hχ j r hj hr m n hm hn x⁻¹ hxinv hxinv1 (p.2⁻¹, p.1⁻¹) hpinv d hd
  simpa only [inv_inv] using Subgroup.inv_mem M.integralPoints hinv

/-- Actual integral lifts of both prescribed opposite factors, preserving
their exact generic images. -/
def integralPrescribedOppositeFactorLift
    (x : M.integralSections)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)))
    (hx1 : M.integralPointMap x ≠ 1)
    (p : rationalPoints G × rationalPoints G)
    (hp : RelativeRoot.IsOppositeFactorPair i a (M.integralPointMap x) p)
    (c d : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X)
    (hc : c ≫ SubgroupFunctor.cellMultiplication j r = x * m⁻¹)
    (hd : d ≫ SubgroupFunctor.cellMultiplication j r = x⁻¹ * m⁻¹) :
    {y : M.integralSections × M.integralSections //
      M.integralPointMap y.1 = p.1 ∧ M.integralPointMap y.2 = p.2} := by
  have h := M.integral_oppositeFactors_of_cell_lifts i hT hroot a ha ν hpos χ hχ
    j r hj hr m n hm hn x hx hx1 p hp c d hc hd
  exact ⟨(Classical.choose h.1, Classical.choose h.2),
    Classical.choose_spec h.1, Classical.choose_spec h.2⟩

end Langlands.GroupScheme.IntegralModel
