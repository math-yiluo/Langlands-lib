/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
public import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Normalization of the actual completed quotient unit

Source: Stacks Tags 03CR, 05RR, 06YY and 0941.
(blueprint: lem-weil-pbc-completed-quotient-unit-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

private theorem quotient_map_eq_Qmap {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] {P Q : CochainComplex B ℤ} (f : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality f
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at h
  simpa only [Category.comp_id, Category.id_comp] using h

private theorem homotopy_map_quotient_eq {B H : Type*} [Category* B] [Category* H]
    [Preadditive B] [Preadditive H] (F : B ⥤ H) [F.Additive]
    {P Q : CochainComplex B ℤ} (f : P ⟶ Q) :
    (F.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map f) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  rfl

section CompletionNormalization
variable {B H : Type*} [Category* B] [Category* H] [Abelian B] [Abelian H]
  [HasDerivedCategory B] [HasDerivedCategory H] [Abelian.HasKInjectiveResolutions H]
  (G : B ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (R : H ⥤ B) [R.Additive] (adj : G ⊣ R)

omit [Abelian.HasKInjectiveResolutions H] in
private theorem exactFactorsh_app_eq (P : CochainComplex B ℤ) :
    G.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      G.mapDerivedCategoryFactors.hom.app P := by
  rw [CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app]
  change G.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
    DerivedCategory.Qh.map (𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem derivedAdjunctionUnit_cochain (P : CochainComplex B ℤ) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        R.rightDerivedFunctor.map (G.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj P)) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) G.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [exactFactorsh_app_eq] at h
  change adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
    R.rightDerivedFunctor.map (G.mapDerivedCategoryFactors.hom.app P) = _ at h
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient, quotient_map_eq_Qmap] at h
  exact h

private theorem completionUnit_normalization
    (F : B ⥤ H) [F.Additive] (LF : DerivedCategory B ⥤ DerivedCategory H)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (β : G ⟶ F) (τ : G.mapDerivedCategory ⟶ LF)
    (P : CochainComplex B ℤ)
    (hτ :
      τ.app (DerivedCategory.Q.obj P) ≫
          ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        G.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex β (.up ℤ)).app P)) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        R.rightDerivedFunctor.map (τ.app (DerivedCategory.Q.obj P)) ≫
        R.rightDerivedFunctor.map (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
        (R.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex β (.up ℤ)).app P)) ≫
        R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
  rw [← R.rightDerivedFunctor.map_comp, hτ, R.rightDerivedFunctor.map_comp,
    ← Category.assoc, derivedAdjunctionUnit_cochain]
  let u := (NatTrans.mapHomologicalComplex β (.up ℤ)).app P
  have h := R.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map u)
  dsimp only [CategoryTheory.Functor.comp_map] at h
  simp only [homotopy_map_quotient_eq, quotient_map_eq_Qmap] at h
  rw [Category.assoc, ← h, ← DerivedCategory.Q.map_comp_assoc]

end CompletionNormalization

private instance constantFunctor_additive
    {B : Type*} [Category* B] [Preadditive B] :
    (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).Additive where
  map_add := by intros; ext n; rfl

private instance limitFunctor_additive
    {B : Type*} [Category* B] [Preadditive B] [HasBinaryProducts B]
    [HasLimitsOfShape ℕᵒᵖ B] : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive :=
  Functor.additive_of_preserves_binary_products _

private def ordinaryAdjUnit
    {B : Type*} [Category* B] [Preadditive B] [HasBinaryProducts B]
    [HasLimitsOfShape ℕᵒᵖ B]
    (F : B ⥤ ℕᵒᵖ ⥤ B) [F.Additive]
    (β : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B) ⟶ F)
    (P : CochainComplex B ℤ) :
    P ⟶ ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  (constLimAdj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
    ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex β (.up ℤ)).app P)

private theorem ordinaryAdjUnit_projection
    {B : Type*} [Category* B] [Preadditive B] [HasBinaryProducts B]
    [HasLimitsOfShape ℕᵒᵖ B]
    (F : B ⥤ ℕᵒᵖ ⥤ B) [F.Additive]
    (β : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B) ⟶ F)
    (P : CochainComplex B ℤ) (q : ℤ) (n : ℕᵒᵖ) :
    (ordinaryAdjUnit F β P).f q ≫ limit.π (F.obj (P.X q)) n =
      (β.app (P.X q)).app n := by
  change (limit.lift _ { pt := P.X q, π := 𝟙 _ } ≫
    limMap (β.app (P.X q))) ≫ limit.π _ n = _
  rw [Category.assoc, limMap_π, limit.lift_π_assoc]
  exact Category.id_comp _

private instance comparisonAbLocallyBijective (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

attribute [local irreducible] completedReductionTower completedReductionTowerCounit
  completedReductionModuleUnit completedReductionTowerUnit

/-- The ordinary strict quotient-limit unit, constructed from the constant/limit
adjunction and the specified quotient augmentation.
Source: Stacks Tags 099M and 0941.
(blueprint: def-weil-pbc-completed-quotient-ordinary-unit). -/
@[irreducible]
def completedQuotientOrdinaryUnit (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
    let := completedReductionModuleTowerFunctor_additive T d
    P ⟶ ((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj
      (((completedReductionModuleTowerFunctor T d).mapHomologicalComplex (.up ℤ)).obj P) := by
  let := completedReductionModuleTowerFunctor_additive T d
  exact ((constLimAdj : completedTowerConstant d T ⊣
    completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).unit.app P ≫
      ((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T) (.up ℤ)).app P)

private theorem completedQuotientOrdinaryUnit_projection (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) (q : ℤ) (n : ℕ) :
    let := completedReductionModuleTowerFunctor_additive T d
    (completedQuotientOrdinaryUnit T d P).f q ≫
        limit.π ((completedReductionModuleTowerFunctor T d).obj (P.X q)) (op n) =
      ((completedReductionModuleUnit d T).app (P.X q)).app (op n) := by
  let := completedReductionModuleTowerFunctor_additive T d
  unfold completedQuotientOrdinaryUnit
  exact ordinaryAdjUnit_projection _ _ P q (op n)

/-- The specified actual quotient-completion unit as a single natural transformation.
Its construction is exactly the derived adjunction unit followed by derived inverse
limit of the fixed quotient augmentation.
Source: Stacks Tags 099M and 0941.
(blueprint: def-weil-pbc-completed-quotient-completion-unit). -/
@[irreducible]
def completedQuotientCompletionUnit (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    𝟭 (d.derived T) ⟶ completedReductionTower T d ⋙
      completedRlim T (d.completedRing T) := by
  letI := reductionModulesHasDerivedCategory T (d.completedRing T)
  letI := reductionTowerHasDerivedCategory T (reductionModuleRing T (d.completedRing T))
  exact (constLimAdj : completedTowerConstant d T ⊣
    completedTowerLimit T (d.completedRing T)).mapDerivedCategoryRightDerivedAdjunction.unit ≫
    CategoryTheory.Functor.whiskerRight (completedReductionTowerUnit d T)
      (completedRlim T (d.completedRing T))

set_option linter.style.haveILetI false in
private theorem actualCompletionUnit_normalization (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := d.completedRing T) P) :
    letI := reductionModulesHasDerivedCategory T (d.completedRing T)
    letI := reductionTowerHasDerivedCategory T (reductionModuleRing T (d.completedRing T))
    let := completedReductionModuleTowerFunctor_additive T d
    let R := completedRlim T (d.completedRing T)
    let L := completedReductionModuleTowerFunctor T d
    ((constLimAdj : completedTowerConstant d T ⊣
      completedTowerLimit T (d.completedRing T)).mapDerivedCategoryRightDerivedAdjunction
        ).unit.app (DerivedCategory.Q.obj P) ≫
        R.map ((completedReductionTowerUnit d T).app (DerivedCategory.Q.obj P)) ≫
        R.map ((completedReductionTowerCounit d T).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Q.map (completedQuotientOrdinaryUnit T d P) ≫
        (completedRlimUnit T (d.completedRing T)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            ((L.mapHomologicalComplex (.up ℤ)).obj P)) := by
  letI := reductionModulesHasDerivedCategory T (d.completedRing T)
  letI := reductionTowerHasDerivedCategory T (reductionModuleRing T (d.completedRing T))
  let := completedReductionModuleTowerFunctor_additive T d
  have ht : HasCompletedReductionTowerUnitNormalization d T
      (completedReductionTowerUnit d T) := by
    unfold completedReductionTowerUnit
    exact (completedReductionTowerUnit_exists d T).exists.choose_spec
  have h := ht P hP
  dsimp only [HasCompletedReductionTowerUnitNormalization, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
    Functor.mapHomotopyCategoryFactors, NatIso.ofComponents, Iso.refl] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  unfold completedQuotientOrdinaryUnit
  exact completionUnit_normalization (completedTowerConstant d T)
    (completedTowerLimit T (d.completedRing T)) constLimAdj
    (completedReductionModuleTowerFunctor T d) (completedReductionTower T d)
    (completedReductionTowerCounit d T) (completedReductionModuleUnit d T)
    (completedReductionTowerUnit d T) P
    h

set_option linter.style.haveILetI false in
/-- On a K-flat representative the actual quotient-completion unit is the localized
strict quotient-unit cone followed by the universal inverse-limit comparison.

Source: Stacks Tags 06YY, 099M and 0941.
(blueprint: lem-weil-pbc-completed-quotient-unit-normalization).

Proof: apply the defining computation formula for the derived constant/limit
adjunction unit. The specified reduction-tower augmentation has its stipulated
normalization on this K-flat representative. Compose that equation with derived
inverse limit. Naturality of its universal comparison moves the ordinary tower
augmentation across the comparison, giving exactly the displayed composite. -/
theorem completedQuotientUnitNormalization
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := d.completedRing T) P) :
    letI := reductionModulesHasDerivedCategory T (d.completedRing T)
    letI := reductionTowerHasDerivedCategory T (reductionModuleRing T (d.completedRing T))
    let := completedReductionModuleTowerFunctor_additive T d
    let R := completedRlim T (d.completedRing T)
    let L := completedReductionModuleTowerFunctor T d
    let ε := derivedCochainCounit L (completedReductionTower T d)
      (completedReductionTowerCounit d T)
    let η := derivedCochainRightUnit (completedTowerLimit T (d.completedRing T)) R
      (completedRlimUnit T (d.completedRing T))
    IsIso (ε.app P) ∧
      (completedQuotientCompletionUnit T d).app (DerivedCategory.Q.obj P) ≫
          R.map (ε.app P) =
        DerivedCategory.Q.map (completedQuotientOrdinaryUnit T d P) ≫
          η.app ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
  letI := reductionModulesHasDerivedCategory T (d.completedRing T)
  letI := reductionTowerHasDerivedCategory T (reductionModuleRing T (d.completedRing T))
  let := completedReductionModuleTowerFunctor_additive T d
  constructor
  · have hp : IsCompletedReductionTowerPair T d (completedReductionTower T d)
        (completedReductionTowerCounit d T) := by
      unfold completedReductionTower completedReductionTowerCounit
      exact (completedReductionTower_exists T d).choose_spec.choose_spec
    simpa only [cochainCounit_app_eq] using hp.2.2 P hP
  · have h := actualCompletionUnit_normalization T d P hP
    simpa only [cochainCounit_app_eq, cochainRightUnit_app_eq,
      completedQuotientCompletionUnit, NatTrans.comp_app,
      CategoryTheory.Functor.whiskerRight_app, Category.assoc] using h

end AlgebraicGeometry.Scheme
