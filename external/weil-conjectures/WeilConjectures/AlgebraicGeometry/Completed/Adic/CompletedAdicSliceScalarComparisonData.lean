/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Universal data for the completed adic slice comparison

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E and 0D6D.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

set_option linter.defProp false in
/-- The universal ordinary and derived scalar-extension witness on the slice.
Its object and map equations determine ordinary tensor extension, while its
counit determines the derived functor.  Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
def completedAdicSliceChangeData (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (R.over U)))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (S.over U)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).map f)

/-- Ordinary scalar extension along the coefficient map restricted to the slice.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
def completedAdicSliceChange (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  (completedAdicSliceChangeData X U f).choose

/-- The chosen slice scalar-extension witness is additive.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
instance completedAdicSliceChange_additive (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    (completedAdicSliceChange X U f).Additive :=
  (completedAdicSliceChangeData X U f).choose_spec.choose_spec.choose_spec.choose

/-- The total left derived scalar-extension functor on the slice.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
def completedAdicSliceDerivedChange (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  (completedAdicSliceChangeData X U f).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose

attribute [local irreducible] completedAdicChangeData completedAdicSliceChangeData

universe u₀ v₀ r₀ m₀

-- The module-sheafification comparison of LocalizedSiteTensorRestriction,
-- used here before introducing any monoidal structure.
section SheafificationComparison

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m₀}]
  [HasWeakSheafify J AddCommGrpCat.{m₀}]
  (R : Sheaf J RingCat.{r₀}) (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m₀}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{m₀}]

private noncomputable def overSheafificationMap (P : PresheafOfModules.{m₀} R.obj) :
    (PresheafOfModules.sheafification (R := R.over U) (𝟙 _)).obj
      ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P) ⟶
        ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P).over U :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
    ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P))

private lemma overSheafificationMap_unit (P : PresheafOfModules.{m₀} R.obj) :
    toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf) ≫
        (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val =
      whiskerLeft (Over.forget U).op (toSheafify J P.presheaf) := by
  have h := (PresheafOfModules.sheafificationHomEquiv (R := R.over U) (𝟙 _)
    (P := (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P)
    (F := ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P).over U)).apply_symm_apply
    ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P))
  exact congrArg ((PresheafOfModules.toPresheaf (R.over U).obj).map) h

private lemma overSheafificationMap_isIso (P : PresheafOfModules.{m₀} R.obj) :
    IsIso (overSheafificationMap R U P) := by
  let a := toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf)
  let b := (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val
  have hi : Presheaf.IsLocallyInjective (J.over U)
      (whiskerLeft (Over.forget U).op (toSheafify J P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  have hs : Presheaf.IsLocallySurjective (J.over U)
      (whiskerLeft (Over.forget U).op (toSheafify J P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  have hi' : Presheaf.IsLocallyInjective (J.over U) b := by
    rw [← Presheaf.comp_isLocallyInjective_iff (J.over U) a b]
    rw [overSheafificationMap_unit]
    exact hi
  have hs' : Presheaf.IsLocallySurjective (J.over U) b := by
    rw [← Presheaf.comp_isLocallySurjective_iff (J.over U) a b]
    rw [overSheafificationMap_unit]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (R.over U))]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · exact (Sheaf.isLocallyInjective_sheafToPresheaf_map_iff _).mp hi'
  · exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).mp hs'

private lemma overSheafificationMap_naturality {P Q : PresheafOfModules.{m₀} R.obj}
    (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (R := R.over U) (𝟙 _)).map
        ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map f) ≫
        overSheafificationMap R U Q =
      overSheafificationMap R U P ≫
        ((PresheafOfModules.sheafification (R := R) (𝟙 _)).map f).over U := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := R.over U) (𝟙 _)
  let push := PresheafOfModules.pushforward (F := Over.forget U) (𝟙 (R.over U).obj)
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [adj, PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    overSheafificationMap, Equiv.apply_symm_apply]
  change push.map f ≫ push.map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app Q) =
    push.map ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P) ≫
      push.map (((SheafOfModules.forget R) ⋙
        PresheafOfModules.restrictScalars (𝟙 R.obj)).map
          ((PresheafOfModules.sheafification (R := R) (𝟙 _)).map f))
  rw [← push.map_comp, ← push.map_comp]
  exact congrArg push.map
    ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.naturality f)

end SheafificationComparison

private abbrev sliceCoefficientMap (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).map f)

private def scalarPresheafMap
    {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r₀} RingCat.{r₀})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r₀}]
    [HasWeakSheafify J AddCommGrpCat.{r₀}]
    {R S : Sheaf J CommRingCat.{r₀}} (f : R ⟶ S)
    {M N : SheafOfModules.{r₀}
      ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj R)}
    (a : M ⟶ N) :
    SheafOfModules.changeOfRingsPresheaf.{v₀, u₀, r₀} f M ⟶
      SheafOfModules.changeOfRingsPresheaf.{v₀, u₀, r₀} f N :=
  { app := fun V ↦ (ModuleCat.extendScalars (f.hom.app V).hom).map (a.val.app V)
    naturality := SheafOfModules.changeOfRingsHom_naturality f M a }

section ScalarNormalization

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r₀} RingCat.{r₀})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r₀}]
  [HasWeakSheafify J AddCommGrpCat.{r₀}]
  {R S : Sheaf J CommRingCat.{r₀}} (f : R ⟶ S)

private def scalarPresheafFunctor :
    SheafOfModules.{r₀}
        ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj R) ⥤
      PresheafOfModules.{r₀}
        ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj S).obj where
  obj := SheafOfModules.changeOfRingsPresheaf f
  map := scalarPresheafMap f
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro V
    simp [scalarPresheafMap]
    rfl
  map_comp a b := by
    apply PresheafOfModules.hom_ext
    intro V
    simp [scalarPresheafMap]

private def scalarNormalizationIso
    (E : SheafOfModules.{r₀}
        ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj R) ⥤
      SheafOfModules.{r₀}
        ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings f M)
    (hm : ∀ {M N} (a : M ⟶ N), E.map a =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom f M a ≫ eqToHom (h N).symm) :
    E ≅ scalarPresheafFunctor f ⋙ PresheafOfModules.sheafification (𝟙 _) :=
  NatIso.ofComponents (fun M ↦ eqToIso (h M)) (by
    intro M N a
    change E.map a ≫ eqToHom (h N) =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom f M a
    rw [hm]
    simp)

end ScalarNormalization

private def scalarOverPresheafIso (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
    SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (sliceCoefficientMap X U f) (M.over U) ≅
      (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} f M) := by
  refine PresheafOfModules.isoMk (fun V ↦ Iso.refl _) ?_
  intro V W g
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    change SheafOfModules.changeOfRingsMap.{t, t + 1, t + 1}
        (sliceCoefficientMap X U f) (M.over U) g (s ⊗ₜ m) =
      SheafOfModules.changeOfRingsMap.{t, t + 1, t + 1}
        f M ((Over.forget U).op.map g) (s ⊗ₜ m)
    exact (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{t, t + 1, t + 1}
      (sliceCoefficientMap X U f) (M.over U) g) s m).trans
      (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{t, t + 1, t + 1}
        f M ((Over.forget U).op.map g)) s m).symm
  | add x y hx hy => simpa only [_root_.map_add] using congrArg₂ (· + ·) hx hy

private theorem globalCounit_isIso (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    (P : CochainComplex (reductionModules X R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso ((reductionDerivedCounit X f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (reductionDerivedExistence X f).choose_spec.choose_spec.2.2 P hP

private abbrev sliceModules (X : Scheme.{t}) (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) :=
  SheafOfModules.{t + 1} ((sheafCompose ((ProEt.topology X).over U)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (R.over U))

private instance sliceModulesDerived (X : Scheme.{t}) (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) :
    HasDerivedCategory (sliceModules X U R) := HasDerivedCategory.standard _

private instance sliceSmall (X : Scheme.{t}) (U : X.ProEt) :
    EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _

private def sliceChangeSpec (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    (sliceModules X U R ⥤ sliceModules X U S) → Prop :=
  (fun {B : Type (t + 2)} {P : B → Prop} (_ : ∃ x, P x) ↦ P)
    (completedAdicSliceChangeData X U f)

private theorem sliceChangeExistence (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    ∃ E, sliceChangeSpec X U f E := completedAdicSliceChangeData X U f

private def sliceDerivedSpec (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    (LF : DerivedCategory (sliceModules X U R) ⥤ DerivedCategory (sliceModules X U S)) :
    Prop :=
  ∃ (ε : DerivedCategory.Qh ⋙ LF ⟶
      (completedAdicSliceChange X U f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
    LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (sliceModules X U R) (.up ℤ)) ∧
      (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
      ∀ P : CochainComplex (sliceModules X U R) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := R.over U) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

private theorem sliceDerivedExistence (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    ∃ LF, sliceDerivedSpec X U f LF :=
  (sliceChangeExistence X U f).choose_spec.choose_spec.choose_spec.choose_spec.2.2

private def sliceCounit (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    DerivedCategory.Qh ⋙ completedAdicSliceDerivedChange X U f ⟶
      (completedAdicSliceChange X U f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (sliceDerivedExistence X U f).choose_spec.choose

private theorem sliceCounit_isIso (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    (P : CochainComplex (sliceModules X U R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R.over U) P) :
    IsIso ((sliceCounit X U f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (sliceDerivedExistence X U f).choose_spec.choose_spec.2.2 P hP
attribute [-instance] sliceModulesDerived sliceSmall

private theorem globalChangeObj (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    (M : reductionModules X R) :
    (completedAdicChange X f).obj M = SheafOfModules.changeOfRings f M :=
  (reductionChangeExistence X f).choose_spec.choose M

private theorem globalChangeMap (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    {M N : reductionModules X R} (a : M ⟶ N) :
    (completedAdicChange X f).map a = eqToHom (globalChangeObj X f M) ≫
      SheafOfModules.changeOfRingsHom f M a ≫ eqToHom (globalChangeObj X f N).symm :=
  (reductionChangeExistence X f).choose_spec.choose_spec.choose a

private theorem sliceChangeObj (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    (M : sliceModules X U R) :
    (completedAdicSliceChange X U f).obj M =
      SheafOfModules.changeOfRings (sliceCoefficientMap X U f) M :=
  (sliceChangeExistence X U f).choose_spec.choose M

private theorem sliceChangeMap (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    {M N : sliceModules X U R} (a : M ⟶ N) :
    (completedAdicSliceChange X U f).map a = eqToHom (sliceChangeObj X U f M) ≫
      SheafOfModules.changeOfRingsHom (sliceCoefficientMap X U f) M a ≫
      eqToHom (sliceChangeObj X U f N).symm :=
  (sliceChangeExistence X U f).choose_spec.choose_spec.choose a

/-- Ordinary scalar extension commutes with restriction to the pro-etale slice.
The proof is the presheaf tensor comparison followed by the sheafification
universal property.  This is the ordinary (underived) step in the derived
comparison theorem.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison-underived).
-/
theorem completedAdic_slice_scalarComparison_underived (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    Nonempty
      ((SheafOfModules.overFunctor
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U ⋙
          completedAdicSliceChange X U f) ≅
        (completedAdicChange X f ⋙ SheafOfModules.overFunctor
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) U)) := by
  let O_S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
  let A := PresheafOfModules.sheafification (R := O_S) (𝟙 _)
  let AU := PresheafOfModules.sheafification (R := O_S.over U) (𝟙 _)
  let n := scalarNormalizationIso f (completedAdicChange X f)
    (globalChangeObj X f) (fun a ↦ globalChangeMap X f a)
  let nU := scalarNormalizationIso (sliceCoefficientMap X U f)
    (completedAdicSliceChange X U f)
    (sliceChangeObj X U f) (fun a ↦ sliceChangeMap X U f a)
  have hI (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
      IsIso (overSheafificationMap O_S U
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} f M)) :=
    overSheafificationMap_isIso O_S U _
  refine ⟨isoWhiskerLeft _ nU ≪≫ ?_ ≪≫
    isoWhiskerRight n.symm (SheafOfModules.overFunctor O_S U)⟩
  refine NatIso.ofComponents (fun M ↦
    AU.mapIso (scalarOverPresheafIso X U f M) ≪≫
      asIso (overSheafificationMap O_S U
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} f M))) ?_
  intro M N a
  have hp : scalarPresheafMap (sliceCoefficientMap X U f) (a.over U) ≫
        (scalarOverPresheafIso X U f N).hom =
      (scalarOverPresheafIso X U f M).hom ≫
        (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
          (scalarPresheafMap f a) := by
    ext V x
    rfl
  change AU.map (scalarPresheafMap (sliceCoefficientMap X U f) (a.over U)) ≫
      (AU.map (scalarOverPresheafIso X U f N).hom ≫ overSheafificationMap O_S U _) =
    (AU.map (scalarOverPresheafIso X U f M).hom ≫ overSheafificationMap O_S U _) ≫
      (A.map (scalarPresheafMap f a)).over U
  rw [← Category.assoc, ← AU.map_comp, hp, AU.map_comp, Category.assoc]
  calc
    _ = AU.map (scalarOverPresheafIso X U f M).hom ≫
        (overSheafificationMap O_S U _ ≫ (A.map (scalarPresheafMap f a)).over U) :=
      congrArg (fun k ↦ AU.map (scalarOverPresheafIso X U f M).hom ≫ k)
        (overSheafificationMap_naturality O_S U (scalarPresheafMap f a))
    _ = _ := (Category.assoc _ _ _).symm

-- A counit invertible on a resolving class is universal.  Compare it with
-- the existing resolving-class construction, then detect the comparison on
-- the localization images of the resolving objects.
private theorem leftDerived_of_resolving
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory B)
    [G.CommShift ℤ] [G.IsTriangulated]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ L ⟶ G)
    (P : Set (HomotopyCategory A (.up ℤ)))
    (hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s)
    (hα : ∀ X : HomotopyCategory A (.up ℤ), X ∈ P → IsIso (α.app X)) :
    L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let Q := DerivedCategory.Qh (C := A)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  have hinv (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y)
      (hX : X ∈ P) (hY : Y ∈ P) (hs : W s) : IsIso (G.map s) := by
    have := hα X hX
    have := hα Y hY
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    have he := α.naturality s
    have : IsIso (α.app X ≫ G.map s) := by
      rw [← he]
      change IsIso (L.map (Q.map s) ≫ α.app Y)
      infer_instance
    exact IsIso.of_isIso_comp_left (α.app X) (G.map s)
  obtain ⟨_, L₀, α₀, hL₀, _, h₀⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) G P hres hinv
  have := hL₀
  let τ := L₀.leftDerivedLift α₀ W L α
  have ht (X : HomotopyCategory A (.up ℤ)) (hX : X ∈ P) :
      IsIso (τ.app (Q.obj X)) := by
    have := h₀ X hX
    have := hα X hX
    have : IsIso (τ.app (Q.obj X) ≫ α₀.app X) := by
      rw [Functor.leftDerived_fac_app]
      exact hα X hX
    exact IsIso.of_isIso_comp_right (τ.app (Q.obj X)) (α₀.app X)
  have (X : HomotopyCategory A (.up ℤ)) : IsIso ((whiskerLeft Q τ).app X) := by
    obtain ⟨Y, s, hY, hs⟩ := hres X
    have := ht Y hY
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    have : IsIso (L.map (Q.map s) ≫ τ.app (Q.obj X)) := by
      rw [τ.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (L.map (Q.map s)) (τ.app (Q.obj X))
  have : IsIso (whiskerLeft Q τ) := NatIso.isIso_of_isIso_app _
  have := Localization.full_whiskeringLeft Q W (DerivedCategory B)
  have := Localization.faithful_whiskeringLeft Q W (DerivedCategory B)
  have : IsIso (((whiskeringLeft _ _ (DerivedCategory B)).obj Q).map τ) :=
    inferInstanceAs (IsIso (whiskerLeft Q τ))
  have : IsIso τ := isIso_of_reflects_iso τ
    ((whiskeringLeft _ _ (DerivedCategory B)).obj Q)
  exact (L₀.isLeftDerivedFunctor_iff_isIso_leftDerivedLift α₀ W L α).2 this

private theorem scalarDerived_composites
    {A B AU BU : Type*} [Category A] [Category B] [Category AU] [Category BU]
    [Abelian A] [Abelian B] [Abelian AU] [Abelian BU]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory AU] [HasDerivedCategory BU]
    (E : A ⥤ B) (EU : AU ⥤ BU) (ER : A ⥤ AU) (ES : B ⥤ BU)
    [E.Additive] [EU.Additive] [ER.Additive] [ES.Additive]
    [PreservesFiniteLimits ER] [PreservesFiniteColimits ER]
    [PreservesFiniteLimits ES] [PreservesFiniteColimits ES]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (FU : DerivedCategory AU ⥤ DerivedCategory BU)
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εU : DerivedCategory.Qh ⋙ FU ⟶ EU.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : Set (HomotopyCategory A (.up ℤ)))
    (hres : ∀ K : HomotopyCategory A (.up ℤ),
      ∃ (K' : HomotopyCategory A (.up ℤ)) (s : K' ⟶ K),
        K' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s)
    (hε : ∀ K ∈ P, IsIso (ε.app K))
    (hεU : ∀ K ∈ P, IsIso (εU.app ((ER.mapHomotopyCategory (.up ℤ)).obj K))) :
    ∃ (αU : DerivedCategory.Qh ⋙ (ER.mapDerivedCategory ⋙ FU) ⟶
        (ER ⋙ EU).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (α : DerivedCategory.Qh ⋙ (F ⋙ ES.mapDerivedCategory) ⟶
        (E ⋙ ES).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      (ER.mapDerivedCategory ⋙ FU).IsLeftDerivedFunctor αU
          (HomotopyCategory.quasiIso A (.up ℤ)) ∧
        (F ⋙ ES.mapDerivedCategory).IsLeftDerivedFunctor α
          (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let αU : DerivedCategory.Qh ⋙ (ER.mapDerivedCategory ⋙ FU) ⟶
      (ER ⋙ EU).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight ER.mapDerivedCategoryFactorsh.hom FU ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (ER.mapHomotopyCategory (.up ℤ)) εU ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (ER ⋙ EU)) (.up ℤ)).hom
        DerivedCategory.Qh
  let α : DerivedCategory.Qh ⋙ (F ⋙ ES.mapDerivedCategory) ⟶
      (E ⋙ ES).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight ε ES.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (E.mapHomotopyCategory (.up ℤ)) ES.mapDerivedCategoryFactorsh.hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ ES)) (.up ℤ)).hom
        DerivedCategory.Qh
  refine ⟨αU, α, ?_, ?_⟩
  · apply leftDerived_of_resolving _ _ _ P hres
    intro K hK
    have := hεU K hK
    dsimp only [αU, NatTrans.comp_app, associator_inv_app, associator_hom_app,
      whiskerLeft_app, whiskerRight_app]
    infer_instance
  · apply leftDerived_of_resolving _ _ _ P hres
    intro K hK
    have := hε K hK
    dsimp only [α, NatTrans.comp_app, associator_inv_app, associator_hom_app,
      whiskerLeft_app, whiskerRight_app]
    infer_instance

attribute [local irreducible] completedAdicChange completedAdicDerivedChange
  completedAdicSliceChange completedAdicSliceDerivedChange
  HasDerivedCategory.standard Functor.mapDerivedCategory
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.monoidalCategory

/-- Both derived composites are left derived functors of their ordinary composites.
The composite of exact slice restriction with derived slice extension, and the
composite of derived extension with exact slice restriction, each carry a counit to
the localized ordinary composite exhibiting it as a left derived functor along the
quasi-isomorphisms.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E and 0D6D.
Proof: every complex of R-modules has a flat-term K-flat resolution, and slice
restriction is exact and carries K-flat complexes to K-flat complexes (pullback by
the localization morphism of ringed topoi, Tag 0G7E). The universal counits of both
derived scalar extensions are invertible on K-flat complexes and their ordinary
extensions preserve quasi-isomorphisms between K-flat complexes. Hence both ordinary
composites send quasi-isomorphisms between K-flat complexes to isomorphisms, both
derived composites are computed on K-flat representatives, and the induced counits
are isomorphisms there; a functor with this property is a left derived functor, by
the universal property of the localization restricted to K-flat complexes.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison-derived-data).
-/
theorem completedAdic_slice_scalarComparison_derived_data (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    let O_R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
    let O_S := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
    let A := SheafOfModules O_R
    letI : (SheafOfModules.overFunctor O_R U).Additive := by
      exact (ringedOverFunctor_exactGeneral O_R U).1
    letI : (SheafOfModules.overFunctor O_S U).Additive := by
      exact (ringedOverFunctor_exactGeneral O_S U).1
    letI : (completedAdicChange X f).Additive := completedAdicChange_additive X f
    letI : (completedAdicSliceChange X U f).Additive :=
      completedAdicSliceChange_additive X U f
    letI : HasDerivedCategory A := HasDerivedCategory.standard _
    letI : HasDerivedCategory (SheafOfModules O_S) := HasDerivedCategory.standard _
    letI : HasDerivedCategory (SheafOfModules (O_R.over U)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory (SheafOfModules (O_S.over U)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory
        (SheafOfModules.{t + 1}
          (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
            ((ProEt.topology X).over U)
            (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).obj S))) :=
      HasDerivedCategory.standard _
    let Q_A := DerivedCategory.Qh (C := A)
    let F := completedAdicDerivedChange X f
    let F_U := completedAdicSliceDerivedChange X U f
    let L_U := ringedDerivedRestrictionGeneral O_R U ⋙ F_U
    let L := F ⋙ ringedDerivedRestrictionGeneral O_S U
    let G_U :=
      ((SheafOfModules.overFunctor O_R U ⋙ completedAdicSliceChange X U f).mapHomotopyCategory
        (.up ℤ)) ⋙ DerivedCategory.Qh
    let G :=
      ((completedAdicChange X f ⋙ SheafOfModules.overFunctor O_S U).mapHomotopyCategory
        (.up ℤ)) ⋙ DerivedCategory.Qh
    ∃ (α : Q_A ⋙ L_U ⟶ G_U) (α' : Q_A ⋙ L ⟶ G),
      L_U.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ)) ∧
      L.IsLeftDerivedFunctor α' (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  let O_R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let O_S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
  let A := SheafOfModules.{t + 1} O_R
  let B := SheafOfModules.{t + 1} O_S
  let AU := sliceModules X U R
  let BU := sliceModules X U S
  let : HasDerivedCategory A := HasDerivedCategory.standard _
  let : HasDerivedCategory B := HasDerivedCategory.standard _
  let : HasDerivedCategory AU := sliceModulesDerived X U R
  let : HasDerivedCategory BU := sliceModulesDerived X U S
  let ER := SheafOfModules.overFunctor O_R U
  let ES := SheafOfModules.overFunctor O_S U
  have : ER.Additive := (ringedOverFunctor_exactGeneral O_R U).1
  have : ES.Additive := (ringedOverFunctor_exactGeneral O_S U).1
  have : PreservesFiniteLimits ER := (ringedOverFunctor_exactGeneral O_R U).2.1
  have : PreservesFiniteColimits ER := (ringedOverFunctor_exactGeneral O_R U).2.2
  have : PreservesFiniteLimits ES := (ringedOverFunctor_exactGeneral O_S U).2.1
  have : PreservesFiniteColimits ES := (ringedOverFunctor_exactGeneral O_S U).2.2
  let E := completedAdicChange X f
  let EU := completedAdicSliceChange X U f
  have : E.Additive := completedAdicChange_additive X f
  have : EU.Additive := completedAdicSliceChange_additive X U f
  let F := completedAdicDerivedChange X f
  let FU := completedAdicSliceDerivedChange X U f
  let ε := reductionDerivedCounit X f
  let εU := sliceCounit X U f
  let P : Set (HomotopyCategory A (.up ℤ)) :=
    {K | ∃ T : CochainComplex A ℤ, T.IsKFlatIndependentCoefficients (R := R) ∧
      (HomotopyCategory.quotient A (.up ℤ)).obj T = K}
  have hres (K : HomotopyCategory A (.up ℤ)) :
      ∃ (K' : HomotopyCategory A (.up ℤ)) (s : K' ⟶ K),
        K' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨T', s, hT', _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) T
    exact ⟨_, (HomotopyCategory.quotient A (.up ℤ)).map s, ⟨T', hT', rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hε : ∀ K ∈ P, IsIso (ε.app K) := by
    intro K hK
    obtain ⟨T, hT, hK⟩ := hK
    have hi : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj T)) :=
      globalCounit_isIso X f T hT
    exact hK ▸ hi
  have hεU : ∀ K ∈ P,
      IsIso (εU.app ((ER.mapHomotopyCategory (.up ℤ)).obj K)) := by
    rintro _ ⟨T, hT, rfl⟩
    have hTU := (SheafOfModules.ringedSite_restriction_exact_kflat.{t + 1, t, t + 1}
      (ProEt.topology X) R U).2.2 T hT
    let TU : CochainComplex (sliceModules X U R) ℤ :=
      (ER.mapHomologicalComplex (.up ℤ)).obj T
    have hi := sliceCounit_isIso X U f TU hTU
    let e : (ER.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A (.up ℤ)).obj T) ≅
        (HomotopyCategory.quotient (sliceModules X U R) (.up ℤ)).obj TU :=
      ((ER.mapHomotopyCategoryFactors (.up ℤ)).app T) ≪≫ eqToIso (by rfl)
    exact (NatTrans.isIso_app_iff_of_iso εU e).2 hi
  have h := scalarDerived_composites E EU ER ES F FU ε εU P hres hε hεU
  exact h

end AlgebraicGeometry.Scheme
