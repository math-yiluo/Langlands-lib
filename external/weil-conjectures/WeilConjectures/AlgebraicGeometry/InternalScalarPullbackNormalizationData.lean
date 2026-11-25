/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization
public import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunction
public import WeilConjectures.Topology.ProfiniteCondensedRing

/-! # Data for normalized internal scalar extension and geometric pullback

(1);
Stacks Project, Tags 03EK, 06YS, 06YY, 0G7E, 0D6D, 07A6 and 0B65
(auxiliary; not a blueprint node).

All tensors and derived categories are the ordinary unbounded, uncompleted ones.
The section-derived-category parameters select localizations of the recorded section
module categories; they impose no flatness, boundedness or geometric condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [instance] SheafOfModules.ScalarDerivedPair.extension_additive

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

/-- Comparison of the specified internal scalar functor with an actual section-ring
left-derived pair. SectionScalarNormalized below requires the ordinary balanced-generator
identity and pins the derived comparison by its flat-term K-flat computation counits.
Source: Stacks 03EK, 06YY and 07A6; blueprint integral proper-base-change proof (1)
(auxiliary; not a blueprint node). -/
structure SectionScalarComparison (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) where
  pair : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
    (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
  restriction : V₀ a T ⋙ (ModuleRingedComparison.equivalence Λ T).functor ≅
    (ModuleRingedComparison.equivalence Λ' T).functor ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
  ordinary : extension a T ⋙ (ModuleRingedComparison.equivalence Λ' T).functor ≅
    (ModuleRingedComparison.equivalence Λ T).functor ⋙ pair.extension
  derived : D a T ⋙ (ModuleRingedComparison.derivedEquivalence Λ' T).functor ≅
    (ModuleRingedComparison.derivedEquivalence Λ T).functor ⋙ pair.derived

/-- The ordinary generator and K-flat counit equations for the specified D comparison.
These are properties of the same scalar data used below in both conjugation equations.
Source: Stacks 03EK, 06YY and 07A6; blueprint integral proper-base-change proof (1)
(auxiliary; not a blueprint node). -/
def SectionScalarNormalized (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) : Prop :=
  (∀ (N : Modules Λ' T) (U : T.ProEtᵒᵖ) (x : N.X.obj.obj U),
    (s.restriction.hom.app N).val.app U x = x) ∧
  (∀ (M : Modules Λ T) (U : T.ProEtᵒᵖ)
    (z : (condensedRingObj Λ' T).obj.obj U) (x : M.X.obj.obj U),
    (eqToHom (s.pair.extension_obj
      ((ModuleRingedComparison.equivalence Λ T).functor.obj M))).val.app U
        ((s.ordinary.hom.app M).val.app U
          (internalScalarGenerator (Scheme.ProEt.topology T) (coefficientMap a T) M U z x)) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
          ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).presheaf).app U
            (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,
              ((sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
                (coefficientMap a T)).hom.app U).hom] x)) ∧
  ∀ (P : CochainComplex (Modules Λ T) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ T)
      (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ T)
      (((ModuleRingedComparison.equivalence Λ T).functor).obj (P.X n))) →
    (ModuleRingedComparison.derivedEquivalence Λ' T).functor.map (compute a T P) ≫
        (ModuleRingedComparison.sectionLocalizationComparison Λ' T
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex s.ordinary (.up ℤ)).hom.app P) =
      s.derived.hom.app (DerivedCategory.Q.obj P) ≫
        s.pair.derived.map (ModuleRingedComparison.sectionLocalizationComparison Λ T P).hom ≫
        SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          s.pair.extension s.pair.extension_additive
          s.pair.derived s.pair.counit
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P)

/-- Localization of the section restriction comparison, using the fixed exact functors.
Source: Stacks 07A6; blueprint integral proper-base-change proof (1)
(auxiliary; not a blueprint node). -/
def sectionScalarRestriction (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) :
    V a T ⋙ (ModuleRingedComparison.derivedEquivalence Λ T).functor ≅
      (ModuleRingedComparison.derivedEquivalence Λ' T).functor ⋙
        SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) :=
  (Functor.mapDerivedCategoryCompIso (V₀ a T)
    (ModuleRingedComparison.equivalence Λ T).functor) ≪≫
  Functor.mapDerivedCategoryNatIso s.restriction ≪≫
  (Functor.mapDerivedCategoryCompIso (ModuleRingedComparison.equivalence Λ' T).functor
    (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
        (coefficientMap a T)))).symm

/-- Tensor with the restricted regular coefficient in the existing section derived tensor.
Source: Stacks 06YU; blueprint integral proper-base-change proof (1)
(auxiliary; not a blueprint node). -/
def sectionScalarTensor (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.modules Λ T) ⥤
      DerivedCategory (ModuleRingedComparison.modules Λ T) :=
  (𝟭 _).prod' ((Functor.const _).obj
    ((ModuleRingedComparison.derivedEquivalence Λ T).functor.obj (B a T))) ⋙
      ModuleRingedComparison.tensor Λ T

/-- The exact section equivalence carries the actual coefficient in degree zero to
its section module in degree zero, with the canonical localization and single factors.
Source: Stacks 06YU; blueprint integral proper-base-change proof (1)
(auxiliary; not a blueprint node). -/
def sectionScalarCoefficient (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.obj (B a T) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) :=
  ModuleRingedComparison.sectionLocalizationComparison Λ T
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a T)) ≪≫
    DerivedCategory.Q.mapIso
      (((ModuleRingedComparison.equivalence Λ T).functor.mapCochainComplexSingleFunctor 0).app
        (B₀ a T))

/-- The chosen internal tensor identification, conjugated to sections, is the section
K-flat balanced construction. Its ordinary map sends s tensor x to x tensor s on every
local generator; its derived map has that ordinary map as its K-flat computation.
Source: Stacks 03EK and 06YY; blueprint integral proper-base-change proof (1)
(auxiliary; not a blueprint node). -/
def SectionTensorNormalized (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (t : TensorNormalization a T) : Prop :=
  ∃ o : s.pair.extension ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)),
  (∀ (M : ModuleRingedComparison.modules Λ T) (U : T.ProEtᵒᵖ)
      (z : (ModuleRingedComparison.ring Λ' T).obj.obj U) (x : M.val.obj U),
    (o.hom.app M).val.app U
      ((eqToHom (s.pair.extension_obj M).symm).val.app U
        ((toSheafify (Scheme.ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf
            (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
              (coefficientMap a T)) M).presheaf).app U
              (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,
                ((sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
                  (coefficientMap a T)).hom.app U).hom] x))) =
      ModuleRingedComparison.sectionPureTensor Λ T M
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) U x z) ∧
  ∃ e : s.pair.derived ⋙ SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        sectionScalarTensor a T,
  (∀ (P : CochainComplex (ModuleRingedComparison.modules Λ T) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ T) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ T) (P.X n)) →
    e.hom.app (DerivedCategory.Q.obj P) ≫
        (ModuleRingedComparison.tensor Λ T).map
          (Prod.mkHom (𝟙 _) (sectionScalarCoefficient a T).hom) ≫
        (ModuleRingedComparison.qTensor Λ T).app
          (P, (CochainComplex.singleFunctor _ 0).obj
            ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) ≫
        DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso
          (curriedTensor (ModuleRingedComparison.modules Λ T))
          ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) P).hom =
      (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
          (SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          s.pair.extension s.pair.extension_additive
            s.pair.derived s.pair.counit P) ≫
        (SheafOfModules.scalarRestrictionComparison.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
            (coefficientMap a T))).hom.app
            ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
              s.pair.extension s.pair.extension_additive).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app P)) ∧
  ∀ M : DerivedCategory (Modules Λ T),
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.map (t.derived.hom.app M) ≫
        (ModuleRingedComparison.tensorComparison Λ T).hom.app (M, B a T) =
      (sectionScalarRestriction a T s).hom.app ((D a T).obj M) ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
            (s.derived.hom.app M) ≫
        e.hom.app ((ModuleRingedComparison.derivedEquivalence Λ T).functor.obj M)

/-- The fixed geometric section comparison with the scalar interface's name L.
This only unfolds that name for the actual total derived pullback; its components
are the existing derivedPullComparison, with no new comparison choice.
Source: Stacks 07A6; blueprint integral proper-base-change proof (1)
(auxiliary; not a blueprint node). -/
def scalarSectionPullComparison
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ₀ T)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L Λ₀ f ⋙ (ModuleRingedComparison.derivedEquivalence Λ₀ X).functor ≅
      (ModuleRingedComparison.derivedEquivalence Λ₀ Y).functor ⋙
        ModuleRingedComparison.derivedPullback Λ₀ f := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact ModuleRingedComparison.derivedPullComparison Λ₀ f

/-- The chosen scalar/pullback map is the section-ring K-flat balanced map after the
fixed scalar and geometric comparisons. The ordinary comparison is specified as the
conjugate of the identity restriction/direct-image square. Since the scalar units insert
1 and the geometric adjunction is the specified ringed adjunction, this is exactly
f inverse (x tensor s) mapping to f inverse x tensor f inverse s, using alpha_f.
Source: Stacks 03D7, 0B65, 0D6D and 0G7E; blueprint integral proper-base-change proof (1)
(auxiliary; not a blueprint node). -/
def SectionPullNormalized (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : SectionScalarComparison a X) (sY : SectionScalarComparison a Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) : Prop :=
  ∃ r : ModuleRingedComparison.pushforward Λ' f ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology Y) (coefficientMap a Y)) ≅
        SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
            ModuleRingedComparison.pushforward Λ f,
  (∀ (N : ModuleRingedComparison.modules Λ' X) (U : Y.ProEtᵒᵖ)
      (x : ((ModuleRingedComparison.pushforward Λ' f).obj N).val.obj U),
    (r.hom.app N).val.app U x = x) ∧
  ∃ c : sY.pair.extension ⋙ ModuleRingedComparison.pullback Λ' f ≅
    ModuleRingedComparison.pullback Λ f ⋙ sX.pair.extension,
  (conjugateEquiv (sY.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' f))
    ((ModuleRingedComparison.adjunction Λ f).comp sX.pair.ordinaryAdjunction) c.inv = r.hom) ∧
  ∃ d : sY.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' f ≅
    ModuleRingedComparison.derivedPullback Λ f ⋙ sX.pair.derived,
  (∀ (P : CochainComplex (ModuleRingedComparison.modules Λ Y) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ Y) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ Y) (P.X n)) →
    d.hom.app (DerivedCategory.Q.obj P) ≫
        sX.pair.derived.map
          ((ModuleRingedComparison.pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          sX.pair.extension sX.pair.extension_additive
          sX.pair.derived sX.pair.counit
          (((ModuleRingedComparison.pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) =
      (ModuleRingedComparison.derivedPullback Λ' f).map
        (SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          sY.pair.extension sY.pair.extension_additive
          sY.pair.derived sY.pair.counit P) ≫
        (ModuleRingedComparison.pullback Λ' f).mapDerivedCategoryFactors.hom.app
          ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
              sY.pair.extension sY.pair.extension_additive).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app P)) ∧
  ∀ M : DerivedCategory (Modules Λ Y),
    (ModuleRingedComparison.derivedEquivalence Λ' X).functor.map (b.hom.app M) ≫
        sX.derived.hom.app ((L Λ f).obj M) ≫
        sX.pair.derived.map ((scalarSectionPullComparison Λ f).hom.app M) =
      (scalarSectionPullComparison Λ' f).hom.app ((D a Y).obj M) ≫
        (ModuleRingedComparison.derivedPullback Λ' f).map (sY.derived.hom.app M) ≫
        d.hom.app ((ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj M)

end AlgebraicGeometry.ProEtale.QuotientChange
