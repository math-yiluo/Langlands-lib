import Langlands.AlgebraicGeometry.Picard.DiscreteValuativeSchemeAdapter
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationFactor

/-! # The displayed-base discrete valuative closed-image theorem -/

universe u
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem DiscreteValuativeCriterion.Existence.specializingMap
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S)
    [LocallyOfFiniteType p] (hp : DiscreteValuativeCriterion.Existence p) :
    SpecializingMap p := by
  intro x y h
  by_cases he : p x = y
  · exact ⟨x, specializes_refl x, he⟩
  let φ : S.presheaf.stalk y ⟶ X.residueField x :=
    S.presheaf.stalkSpecializes h ≫ p.stalkMap x ≫ X.residue x
  have hn : ¬ IsLocalHom φ.hom := by
    intro hlocal
    exact he (specializationResidueMap_local_imp_eq p x y h)
  obtain ⟨A, hA, hDVR, hlocal⟩ :=
    DiscreteValuationFactor.exists_discrete_valuation_factor
      (S.presheaf.stalk y) (X.residueField x)
    φ.hom (specializationResidueMap_essFiniteType p x y h) hn
  let φA : S.presheaf.stalk y ⟶ ↧A :=
    CommRingCat.ofHom (φ.hom.codRestrict A.toSubring hA)
  have w : X.fromSpecResidueField x ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x))) ≫
        Spec.map φA ≫ S.fromSpecStalk y := by
    rw [specializationResidueMap_commutes p x y h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  obtain ⟨l, hl₁, hl₂⟩ := (hp
    { R := A, K := X.residueField x, commSq := ⟨w⟩, .. } hDVR).exists_lift
  dsimp only at hl₁ hl₂
  refine ⟨l (closedPoint A), ?_, ?_⟩
  · simp_rw [← Scheme.fromSpecResidueField_apply x (closedPoint (X.residueField x)), ← hl₁]
    exact (specializes_closedPoint _).map l.continuous
  · rw [← Scheme.Hom.comp_apply, hl₂]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have hc : Spec.map φA (closedPoint A) = closedPoint (S.presheaf.stalk y) :=
      comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
    rw [hc, S.fromSpecStalk_closedPoint]

/-- Discrete valuative existence gives closed images of closed irreducible subsets. -/
theorem discreteValuativeClosedIrreducibleImages :
    DiscreteValuativeClosedIrreducibleImagesStatement.{u} := by
  intro X S _ p _ _ hp
  exact (closedIrreducibleImages_iff_specializingMap p).mpr
    (DiscreteValuativeCriterion.Existence.specializingMap p hp)

end Langlands.AlgebraicGeometry
