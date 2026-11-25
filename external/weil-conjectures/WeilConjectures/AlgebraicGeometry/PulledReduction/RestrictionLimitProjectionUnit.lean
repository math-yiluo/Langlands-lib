/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PulledReduction.PulledReductionComparisonData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Restriction of derived limits and constant units

## References

* Stacks 06YY, 07A4, and 099N(5)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryNatIso
private theorem normalized_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (α : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (hα : ∀ P : CochainComplex B ℤ,
      G.mapDerivedCategory.map (_root_.chainDerivedUnit R P) ≫
          α.app (DerivedCategory.Q.obj P) ≫
          R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app P) =
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app P) ≫
          _root_.chainDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj P)) :
    α = (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom)) := by
  apply _root_.derived_comp_ext R G
  intro P
  apply (cancel_mono (R'.rightDerivedFunctor.map
    (H.mapDerivedCategoryFactors.hom.app P))).mp
  simpa only [Functor.mapDerivedCategorySquareIso, Category.assoc] using
    (hα P).trans (_root_.derived_mate_factors adj adj' s P).symm

private theorem derivedUnit_complex
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (P : CochainComplex C ℤ) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) ≫
        R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          ((L.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app P) := by
  have h : adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
        (DerivedCategory.Q.obj P) ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ _).obj P)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P)) ≫
      R.rightDerivedFunctorUnit.app (((L.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P))) :=
    (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj P)
  apply (cancel_mono (R.rightDerivedFunctor.map
    (L.mapDerivedCategoryFactors.hom.app P))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [R.rightDerivedFunctor.map_id, Category.comp_id]
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    _root_.quotient_hom_id, _root_.quotient_inv_id,
    _root_.homotopyFactors_inv_id] at h
  erw [L.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id] at h
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  have hu : (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  change _ = DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫ _ at h
  rw [hu] at h
  erw [Category.comp_id] at h
  exact h

namespace AlgebraicGeometry.Scheme.PulledReduction
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [local irreducible] OrderedExchange.lambda

private theorem projection_unit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (J : CochainComplex (reductionTowerCategory T (reductionModuleRing T R)) ℤ)
    (n : ℕ) :
    (completedRlimUnit T R).app ((HomotopyCategory.quotient _ _).obj J) ≫
        (completedRlimProjection T R n).app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app J) ≫
        (reductionTowerEvaluation T (reductionModuleRing T R) n).mapDerivedCategoryFactors.inv.app
          J := by
  dsimp only [completedRlimUnit, completedRlimProjection, NatTrans.comp_app]
  rw [← Category.assoc]
  erw [Functor.rightDerivedNatTrans_app]
  rw [Category.assoc]
  have h := NatTrans.congr_app
    (Functor.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      (reductionTowerEvaluation T (reductionModuleRing T R) n))
    ((HomotopyCategory.quotient _ _).obj J)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  erw [h]
  simp only [Functor.mapDerivedCategoryFactorsh,
    Functor.mapHomologicalComplexUpToQuasiIsoFactorsh,
    NatTrans.mapHomotopyCategory, Functor.whiskerRight_app]
  simp
  rfl

private theorem ordinaryProjection (T : Scheme.{t})
    (P : CochainComplex (d.towers T) ℤ) (n : ℕ) :
    (NatIso.mapHomologicalComplex (OrderedExchange.ordinaryLambda d T) (.up ℤ)).hom.app P ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          (((tres d T).mapHomologicalComplex (.up ℤ)).obj P) =
      ((res d T).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app P) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact (OrderedExchange.ordinaryLambda_existsUnique d T).exists.choose_spec (P.X i) n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] mateEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantUnit_eq (T : Scheme.{t}) :
    completedConstantRlimUnit d T =
      (constLimAdj : d.constantTower T ⊣ completedTowerLimit T
          (d.completedRing T)).mapDerivedCategoryRightDerivedAdjunction.unit := by
  apply (completedConstantRlimUnit_exists d T).unique
    (completedConstantRlimUnit_exists d T).exists.choose_spec
  intro P
  simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact derivedUnit_complex (d.constantTower T)
    (completedTowerLimit T (d.completedRing T)) constLimAdj P

end AlgebraicGeometry.Scheme.PulledReduction
