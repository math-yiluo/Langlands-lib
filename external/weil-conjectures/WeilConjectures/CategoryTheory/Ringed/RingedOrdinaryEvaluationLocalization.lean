/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import all WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import all WeilConjectures.SixFunctors.SfbHomFilteredColimit.DerivedInternalHomFilteredColimitData
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Unsigned ordinary evaluation and its derived localization

Source: Stacks Project, sites-cohomology.tex, Tags 08JD, 08JE, 0A98 and Section 0A8X
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization).

The formulas use the recorded sheafified tensor generators, Hom-product projections,
coefficient-unit identifications, and fixed K-injective augmentation. The ordinary map
exists for arbitrary complexes; only its derived comparison requires the stated K-flatness
and augmentation quasi-isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- Evaluate the actual Hom-product projection at the identity of the localized site.
Source: Stacks Section 0A8X, Tag 08JE
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedOrdinaryHomValue
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (n a b : ℤ) (h : a + n = b) (U : Cᵒᵖ)
    (φ : ((homComplex (R := R) E F).X n).val.obj U) (x : (E.X a).val.obj U) :
    (F.X b).val.obj U :=
  coefficientHomSectionApply.{u, c, v} J R (E.X a) (F.X b) U
    ((coefficientHomComponent.{u, c, v} J R E F n a b h).val.app U φ) x

/-- Extract the coefficient from the supported component of the ordinary dual.
Both transports are the actual degree-zero coefficient-unit identifications.
Source: Stacks Section 0A8X, Tag 08JE
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedOrdinaryDualValue
    (E : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (q a : ℤ) (h : a + q = 0) (U : Cᵒᵖ)
    (φ : ((homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)).X q).val.obj U)
    (x : (E.X a).val.obj U) : R.obj.obj U :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))).hom.val.app U)
    (ringedOrdinaryHomValue.{c, v, u} J R E (ringedTensorUnitComplex.{c, v, u} J R)
      q a 0 h U φ x)

/-- The unsigned formula on every sheafified tensor generator and Hom projection.
Supported components act by the actual coefficient scalar; all other components vanish.
The equality `hp` only transports between equal integer degrees.
Source: Stacks Tag 08JE, Section 0A8X
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def RingedOrdinaryEvaluationFormula
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (aEF : (coefficientTotalTensor.{u, c, v} J R).obj
      (F, homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ⟶
        homComplex (R := R) E F) : Prop :=
  ∀ (p q n a b : ℤ) (hn : p + q = n) (hb : a + n = b) (U : Cᵒᵖ)
    (y : (F.X p).val.obj U)
    (φ : ((homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)).X q).val.obj U)
    (x : (E.X a).val.obj U),
    (∀ (h : a + q = 0) (hp : p = b),
      ringedOrdinaryHomValue.{c, v, u} J R E F n a b hb U
        ((aEF.f n).val.app U (coefficientTensorGenerator.{u, c, v} J R F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
          p q n hn U y φ)) x =
      (eqToHom (congrArg F.X hp)).val.app U
        (ringedOrdinaryDualValue.{c, v, u} J R E q a h U φ x • y)) ∧
    (a + q ≠ 0 →
      ringedOrdinaryHomValue.{c, v, u} J R E F n a b hb U
        ((aEF.f n).val.app U (coefficientTensorGenerator.{u, c, v} J R F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
          p q n hn U y φ)) x = 0)

/-- Apply ordinary Hom to the fixed augmentation already used to define derived Hom.
Source: Stacks Tags 0A95 and 08J9
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedHomAugmentationMap
    (E G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    homComplex (R := R) E G ⟶
      homComplex (R := R) E ((coefficientHomResolution.{u, c, v} J R).obj G) :=
  (homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op E) |>.map
    ((coefficientHomAugmentation.{u, c, v} J R).app G)

section DerivedDefinitions

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- The comparison induced by the fixed augmentation and localization factorization.
Source: Stacks Tags 0A95 and 08J9
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedOrdinaryHomComparison
    (E G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    DerivedCategory.Q.obj (homComplex (R := R) E G) ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj G) :=
  DerivedCategory.Q.map (ringedHomAugmentationMap.{c, v, u} J R E G) ≫
    (coefficientHomResolutionIso.{u, c, v, w} J R E G).inv

/-- The transpose of reassociation, coefficient evaluation and the right unit action.
The coefficient object is identified with the monoidal unit by the recorded coherence.
Source: Stacks Tags 08JD, 08JE and 0A98
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedDualTensorHom
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (unitIso : S.monoidal.tensorUnit ≅
      DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))
    (A B : DerivedCategory (RingedTensorModules.{c, v, u} J R)) :
    S.tensor.obj (B, (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
      (op A, DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op A, B) :=
  S.transpose _ A B
    ((S.monoidal.associator B
      ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op A, DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) A).hom ≫
      (@MonoidalCategory.tensorLeft _ _ S.monoidal B).map (S.evaluation A
        (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) ≫
      (@MonoidalCategory.tensorLeft _ _ S.monoidal B).map unitIso.inv ≫
      (S.monoidal.rightUnitor B).hom)

end DerivedDefinitions

section OrdinaryHelpers

set_option linter.unusedSectionVars false

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

open MonoidalCategory CochainComplex

attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 4000] HomologicalComplex.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric
attribute [local instance 1000] RingedDerivedNative.baseLimits RingedDerivedNative.baseColimits
  RingedDerivedNative.gradedTensor RingedDerivedNative.gradedTensorFour
  RingedDerivedNative.gradedTensorLeft RingedDerivedNative.gradedTensorRight
  RingedDerivedNative.baseClosed RingedDerivedNative.auxTensorLeftColimits
  RingedDerivedNative.auxTensorRightColimits
attribute [local instance] SheafOfModules.cochainModulesPreadditive
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

set_option hygiene false in
local notation "Mod" => RingedDerivedNative.Modules.{c, v, u} J R

@[no_expose]
private noncomputable def ordinaryPure (A B : Mod) (U : Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) : (A ⊗ B).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{max c v u}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)).unit.app
      (A.val ⊗ B.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv.val).app U)
    (x ⊗ₜ[R.obj.obj U] y)

private theorem ordinaryTotalHom_ext (P Q : CochainComplex Mod ℤ)
    (A B : Mod) (n : ℤ)
    (f g : ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)).X n ⟶
      SheafOfModules.homObj (R := R) A B)
    (h : ∀ (p q : ℤ) (hpq : p + q = n) (U : Cᵒᵖ)
      (y : (P.X p).val.obj U) (φ : (Q.X q).val.obj U) (x : A.val.obj U),
      coefficientHomSectionApply.{u, c, v} J R A B U
        (f.val.app U (coefficientTensorGenerator.{u, c, v} J R P Q p q n hpq U y φ)) x =
      coefficientHomSectionApply.{u, c, v} J R A B U
        (g.val.app U (coefficientTensorGenerator.{u, c, v} J R P Q p q n hpq U y φ)) x) :
    f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := P) (K₂ := Q)
    (F := curriedTensor Mod) (c := .up ℤ)
  intro p q hpq
  apply WeilConjectures.SfbHomFilteredColimit.tensor_to_homObj_ext.{c, v, u}
    J R (P.X p) (Q.X q) A B
  exact h p q hpq

private theorem ordinaryPure_map {A A' B B' : Mod} (f : A ⟶ A') (g : B ⟶ B')
    (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (f ⊗ₘ g).val.app U (ordinaryPure.{c, v, u} J R A B U x y) =
      ordinaryPure.{c, v, u} J R A' B' U (f.val.app U x) (g.val.app U y) := by
  exact WeilConjectures.SfbHomFilteredColimit.pure_map.{c, v, u} J R f g U x y

private theorem ordinaryTotal_map
    {P P' Q Q' : CochainComplex Mod ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (coefficientTotalTensor.{u, c, v} J R).map (X := (P, Q)) (Y := (P', Q')) (f, g) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ) := by
  erw [RingedDerivedNative.totalTensor_map_eq.{c, v, u} J R P' P Q' Q f g]
  rfl

private theorem ordinaryGenerator_map
    {P P' Q Q' : CochainComplex Mod ℤ} (f : P ⟶ P') (g : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{u, c, v} J R).map
      (X := (P, Q)) (Y := (P', Q')) (f, g)).f n).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P Q p q n h U x y) =
      coefficientTensorGenerator.{u, c, v} J R P' Q' p q n h U
        ((f.f p).val.app U x) ((g.f q).val.app U y) := by
  have hm := ordinaryTotal_map.{c, v, u} J R f g
  have hme := congrArg (fun k ↦ (k.f n).val.app U
    (coefficientTensorGenerator.{u, c, v} J R P Q p q n h U x y)) hm
  apply hme.trans
  change ((HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).f n).val.app U
      ((HomologicalComplex.ιMapBifunctor P Q (curriedTensor Mod)
        (.up ℤ) p q n h).val.app U (ordinaryPure.{c, v, u} J R (P.X p) (Q.X q) U x y)) =
    (HomologicalComplex.ιMapBifunctor P' Q' (curriedTensor Mod)
      (.up ℤ) p q n h).val.app U
        (ordinaryPure.{c, v, u} J R (P'.X p) (Q'.X q) U
          ((f.f p).val.app U x) ((g.f q).val.app U y))
  have hi := HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor Mod)
    (.up ℤ) p q n h
  simp only [curriedTensor_map_app, curriedTensor_obj_map] at hi
  rw [← Category.assoc, ← tensorHom_def] at hi
  have he := congrArg (fun k ↦ k.val.app U
    (ordinaryPure.{c, v, u} J R (P.X p) (Q.X q) U x y)) hi
  change ((HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).f n).val.app U
      ((HomologicalComplex.ιMapBifunctor P Q (curriedTensor Mod)
        (.up ℤ) p q n h).val.app U (ordinaryPure.{c, v, u} J R (P.X p) (Q.X q) U x y)) =
    (HomologicalComplex.ιMapBifunctor P' Q' (curriedTensor Mod)
      (.up ℤ) p q n h).val.app U
        ((f.f p ⊗ₘ g.f q).val.app U
          (ordinaryPure.{c, v, u} J R (P.X p) (Q.X q) U x y)) at he
  rw [ordinaryPure_map.{c, v, u}] at he
  exact he

private theorem ordinaryGenerator_zero_right
    (P Q : CochainComplex Mod ℤ) (p q n : ℤ) (h : p + q = n)
    (U : Cᵒᵖ) (x : (P.X p).val.obj U) :
    coefficientTensorGenerator.{u, c, v} J R P Q p q n h U x 0 = 0 := by
  unfold coefficientTensorGenerator
  simp only [TensorProduct.tmul_zero]
  change (HomologicalComplex.ιMapBifunctor P Q (curriedTensor Mod) (.up ℤ) p q n h).val.app U
    ((((PresheafOfModules.sheafificationAdjunction.{max c v u} (𝟙 _)).unit.app
      ((P.X p).val ⊗ (Q.X q).val) ≫
      (SheafOfModules.tensorObjIsoSheafification (R := R) (P.X p) (Q.X q)).inv.val).app U) 0) = 0
  simp only [map_zero]

@[no_expose]
private noncomputable def ordinaryCurry
    (P E F : CochainComplex Mod ℤ) :
    ((coefficientTotalTensor.{u, c, v} J R).obj (P, E) ⟶ F) ≃
      (P ⟶ homComplex (R := R) E F) :=
  RingedDerivedNative.chainEquiv.{c, v, u} J R P E F

attribute [local irreducible] ordinaryCurry

private theorem ordinaryCurry_symm_spec
    (P E F : CochainComplex Mod ℤ) (g : P ⟶ homComplex (R := R) E F) :
    IsCoefficientTensorCurry.{u, c, v} J R P E F
      ((ordinaryCurry.{c, v, u} J R P E F).symm g) g := by
  intro p a U y x
  simpa only [ordinaryCurry, coefficientHomSectionApply, coefficientHomComponent,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] using
    RingedDerivedNative.chainEquiv_symm_pure.{c, v, u, w} J R P E F g
      p a (p + a) rfl (add_comm a p) U y x

private theorem ordinaryCurry_spec (P E F : CochainComplex Mod ℤ)
    (f : (coefficientTotalTensor.{u, c, v} J R).obj (P, E) ⟶ F) :
    IsCoefficientTensorCurry.{u, c, v} J R P E F f (ordinaryCurry.{c, v, u} J R P E F f) := by
  simpa only [Equiv.symm_apply_apply] using
    ordinaryCurry_symm_spec.{c, v, u} J R P E F (ordinaryCurry.{c, v, u} J R P E F f)

private theorem ordinaryCurry_symm_apply
    (P E F : CochainComplex Mod ℤ) (g : P ⟶ homComplex (R := R) E F)
    (p a n : ℤ) (h : p + a = n) (h' : a + p = n)
    (U : Cᵒᵖ) (y : (P.X p).val.obj U) (x : (E.X a).val.obj U) :
    (((ordinaryCurry.{c, v, u} J R P E F).symm g).f n).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P E p a n h U y x) =
      coefficientHomSectionApply.{u, c, v} J R (E.X a) (F.X n) U
        ((coefficientHomComponent.{u, c, v} J R E F p a n h').val.app U
          ((g.f p).val.app U y)) x := by
  subst n
  exact ordinaryCurry_symm_spec.{c, v, u} J R P E F g p a U y x

private theorem ordinaryCurry_apply
    (P E F : CochainComplex Mod ℤ)
    (f : (coefficientTotalTensor.{u, c, v} J R).obj (P, E) ⟶ F)
    (p a n : ℤ) (h : p + a = n) (h' : a + p = n)
    (U : Cᵒᵖ) (y : (P.X p).val.obj U) (x : (E.X a).val.obj U) :
    coefficientHomSectionApply.{u, c, v} J R (E.X a) (F.X n) U
        ((coefficientHomComponent.{u, c, v} J R E F p a n h').val.app U
          (((ordinaryCurry.{c, v, u} J R P E F f).f p).val.app U y)) x =
      (f.f n).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P E p a n h U y x) := by
  subst n
  exact (ordinaryCurry_spec.{c, v, u} J R P E F f p a U y x).symm

private theorem ordinaryUnit_zero (n : ℤ) (hn : n ≠ 0) (U : Cᵒᵖ)
    (x : ((ringedTensorUnitComplex.{c, v, u} J R).X n).val.obj U) : x = 0 := by
  have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) n hn
  have hi := hz.eq_of_src (𝟙 _) 0
  exact congrArg (fun f ↦ f.val.app U x) hi

private theorem ordinaryIterated_ext (P Q L I : CochainComplex Mod ℤ)
    (f g : (coefficientTotalTensor.{u, c, v} J R).obj
      ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q), L) ⟶ I)
    (h : ∀ (p q n a b : ℤ) (hpq : p + q = n) (hab : a + n = b)
      (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U)
      (z : (L.X a).val.obj U),
      (f.f b).val.app U
        (coefficientTensorGenerator.{u, c, v} J R
          ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L n a b (by omega) U
          (coefficientTensorGenerator.{u, c, v} J R P Q p q n hpq U x y) z) =
      (g.f b).val.app U
        (coefficientTensorGenerator.{u, c, v} J R
          ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L n a b (by omega) U
          (coefficientTensorGenerator.{u, c, v} J R P Q p q n hpq U x y) z)) : f = g := by
  apply (ordinaryCurry.{c, v, u} J R
    ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L I).injective
  apply HomologicalComplex.hom_ext
  intro n
  apply homComplex_hom_ext
  intro a b hab
  apply ordinaryTotalHom_ext.{c, v, u} J R P Q (L.X a) (I.X b) n
  intro p q hpq U x y z
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change ringedOrdinaryHomValue.{c, v, u} J R L I n a b hab U
      (((ordinaryCurry.{c, v, u} J R _ L I f).f n).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P Q p q n hpq U x y)) z =
    ringedOrdinaryHomValue.{c, v, u} J R L I n a b hab U
      (((ordinaryCurry.{c, v, u} J R _ L I g).f n).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P Q p q n hpq U x y)) z
  unfold ringedOrdinaryHomValue
  rw [ordinaryCurry_apply.{c, v, u}, ordinaryCurry_apply.{c, v, u}]
  exact h p q n a b hpq hab U x y z

@[no_expose]
private noncomputable def ordinaryAssociator (P Q L : CochainComplex Mod ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj
        ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q), L) ≅
      (coefficientTotalTensor.{u, c, v} J R).obj
        (P, (coefficientTotalTensor.{u, c, v} J R).obj (Q, L)) :=
  HomologicalComplex.associator P Q L

@[no_expose]
private noncomputable def ordinaryRightUnitor (P : CochainComplex Mod ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj
      (P, ringedTensorUnitComplex.{c, v, u} J R) ≅ P :=
  by
    with_unfolding_all exact HomologicalComplex.rightUnitor P

private theorem ordinaryAssociator_apply
    (P Q L : CochainComplex Mod ℤ)
    (p q a n r b : ℤ) (hpq : p + q = n) (hqa : q + a = r)
    (hn : n + a = b) (hb : p + r = b) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (L.X a).val.obj U) :
    (((ordinaryAssociator.{c, v, u} J R P Q L).hom).f b).val.app U
      (coefficientTensorGenerator.{u, c, v} J R
        ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L n a b hn U
        (coefficientTensorGenerator.{u, c, v} J R P Q p q n hpq U x y) z) =
    coefficientTensorGenerator.{u, c, v} J R P
      ((coefficientTotalTensor.{u, c, v} J R).obj (Q, L)) p r b hb U x
      (coefficientTensorGenerator.{u, c, v} J R Q L q a r hqa U y z) := by
  exact (RingedDerivedNative.complexConstraints.{c, v, u} J R).associator
    P Q L p q a n r b hpq hqa hn hb U x y z

private theorem ordinaryRightUnitor_apply
    (P : CochainComplex Mod ℤ) (n : ℤ) (h : n + 0 = n) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : (P.X n).val.obj U) :
    (((ordinaryRightUnitor.{c, v, u} J R P).hom).f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J R P
        (ringedTensorUnitComplex.{c, v, u} J R) n 0 n h U x
        (ringedTensorUnitSection.{c, v, u} J R U a)) = a • x := by
  with_unfolding_all
    exact (RingedDerivedNative.complexConstraints.{c, v, u} J R).rightUnitor P n h U a x

attribute [local irreducible] ordinaryAssociator ordinaryRightUnitor
  coefficientTotalTensor coefficientTensorGenerator

private theorem ordinaryAssociator_unique
    (P Q L : CochainComplex Mod ℤ)
    (f : (coefficientTotalTensor.{u, c, v} J R).obj
        ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q), L) ⟶
      (coefficientTotalTensor.{u, c, v} J R).obj
        (P, (coefficientTotalTensor.{u, c, v} J R).obj (Q, L)))
    (hf : ∀ (p q a n r b : ℤ) (hpq : p + q = n) (hqa : q + a = r)
      (hn : n + a = b) (hb : p + r = b) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (L.X a).val.obj U),
      (f.f b).val.app U (coefficientTensorGenerator.{u, c, v} J R
        ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L n a b hn U
        (coefficientTensorGenerator.{u, c, v} J R P Q p q n hpq U x y) z) =
      coefficientTensorGenerator.{u, c, v} J R P
        ((coefficientTotalTensor.{u, c, v} J R).obj (Q, L)) p r b hb U x
        (coefficientTensorGenerator.{u, c, v} J R Q L q a r hqa U y z)) :
    f = (ordinaryAssociator.{c, v, u} J R P Q L).hom := by
  apply ordinaryIterated_ext.{c, v, u} J R P Q L
  intro p q n a b hn hb U x y z
  exact (hf p q a n (q + a) b hn rfl (by omega) (by omega) U x y z).trans
    (ordinaryAssociator_apply.{c, v, u} J R
      P Q L p q a n (q + a) b hn rfl (by omega) (by omega) U x y z).symm

private theorem ordinaryRightUnitor_unique (P : CochainComplex Mod ℤ)
    (f : (coefficientTotalTensor.{u, c, v} J R).obj
      (P, ringedTensorUnitComplex.{c, v, u} J R) ⟶ P)
    (hf : ∀ (n : ℤ) (h : n + 0 = n) (U : Cᵒᵖ) (a : R.obj.obj U)
      (x : (P.X n).val.obj U),
      (f.f n).val.app U (coefficientTensorGenerator.{u, c, v} J R P
        (ringedTensorUnitComplex.{c, v, u} J R) n 0 n h U x
        (ringedTensorUnitSection.{c, v, u} J R U a)) = a • x) :
    f = (ordinaryRightUnitor.{c, v, u} J R P).hom := by
  apply WeilConjectures.coefficient_total_ext.{u, c, v} J R P
    (ringedTensorUnitComplex.{c, v, u} J R) P
  intro p q U x z
  by_cases hq : q = 0
  · subst q
    let e := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))
    have he : e.inv.val.app U (e.hom.val.app U z) = z :=
      congrArg (fun k ↦ k.val.app U z) e.hom_inv_id
    have hh := (hf p (add_zero p) U (e.hom.val.app U z) x).trans
      (ordinaryRightUnitor_apply.{c, v, u} J R
        P p (add_zero p) U (e.hom.val.app U z) x).symm
    change (f.f p).val.app U (coefficientTensorGenerator.{u, c, v} J R P
        (ringedTensorUnitComplex.{c, v, u} J R) p 0 p (add_zero p) U x
        (e.inv.val.app U (e.hom.val.app U z))) = _ at hh
    change (f.f p).val.app U (coefficientTensorGenerator.{u, c, v} J R P
        (ringedTensorUnitComplex.{c, v, u} J R) p 0 p (add_zero p) U x
        (e.inv.val.app U (e.hom.val.app U z))) =
      ((ordinaryRightUnitor.{c, v, u} J R P).hom.f p).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P
          (ringedTensorUnitComplex.{c, v, u} J R) p 0 p (add_zero p) U x
          (e.inv.val.app U (e.hom.val.app U z))) at hh
    change (f.f (p + 0)).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P
          (ringedTensorUnitComplex.{c, v, u} J R) p 0 (p + 0) rfl U x z) =
      ((ordinaryRightUnitor.{c, v, u} J R P).hom.f (p + 0)).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P
          (ringedTensorUnitComplex.{c, v, u} J R) p 0 (p + 0) rfl U x z)
    rw [he] at hh
    have hh' : ∀ (n : ℤ) (hn : p + 0 = n),
        (f.f n).val.app U
            (coefficientTensorGenerator.{u, c, v} J R P
              (ringedTensorUnitComplex.{c, v, u} J R) p 0 n hn U x z) =
          ((ordinaryRightUnitor.{c, v, u} J R P).hom.f n).val.app U
            (coefficientTensorGenerator.{u, c, v} J R P
              (ringedTensorUnitComplex.{c, v, u} J R) p 0 n hn U x z) := by
      intro n hn
      have hnp : n = p := by omega
      cases hnp
      exact hh
    exact hh' (p + 0) rfl
  · rw [ordinaryUnit_zero.{c, v, u} J R q hq U z,
      ordinaryGenerator_zero_right.{c, v, u}, map_zero, map_zero]

@[no_expose]
private noncomputable def ordinaryEvaluation
    (E F : CochainComplex Mod ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj
        (F, homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ⟶
      homComplex (R := R) E F :=
  let D := homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)
  let ev := (ordinaryCurry.{c, v, u} J R D E (ringedTensorUnitComplex.{c, v, u} J R)).symm (𝟙 D)
  ordinaryCurry.{c, v, u} J R ((coefficientTotalTensor.{u, c, v} J R).obj (F, D)) E F
    ((ordinaryAssociator.{c, v, u} J R F D E).hom ≫ (coefficientTotalTensor.{u, c, v} J R).map
      (X := (F, (coefficientTotalTensor.{u, c, v} J R).obj (D, E)))
      (Y := (F, ringedTensorUnitComplex.{c, v, u} J R)) (𝟙 F, ev) ≫
      (ordinaryRightUnitor.{c, v, u} J R F).hom)

private theorem ordinaryEvaluation_eq (E F : CochainComplex Mod ℤ) :
    ordinaryEvaluation.{c, v, u} J R E F =
      let D := homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)
      let ev := (ordinaryCurry.{c, v, u} J R D E
        (ringedTensorUnitComplex.{c, v, u} J R)).symm (𝟙 D)
      ordinaryCurry.{c, v, u} J R ((coefficientTotalTensor.{u, c, v} J R).obj (F, D)) E F
        ((ordinaryAssociator.{c, v, u} J R F D E).hom ≫ (coefficientTotalTensor.{u, c, v} J R).map
          (X := (F, (coefficientTotalTensor.{u, c, v} J R).obj (D, E)))
          (Y := (F, ringedTensorUnitComplex.{c, v, u} J R)) (𝟙 F, ev) ≫
          (ordinaryRightUnitor.{c, v, u} J R F).hom) := rfl

attribute [local irreducible] ordinaryEvaluation

private theorem ordinaryEvaluation_formula (E F : CochainComplex Mod ℤ) :
    RingedOrdinaryEvaluationFormula.{c, v, u} J R E F (ordinaryEvaluation.{c, v, u} J R E F) := by
  intro p q n a b hn hb U y φ x
  let O := ringedTensorUnitComplex.{c, v, u} J R
  let D := homComplex (R := R) E O
  let P := (coefficientTotalTensor.{u, c, v} J R).obj (F, D)
  let ev := (ordinaryCurry.{c, v, u} J R D E O).symm (𝟙 D)
  let c : (coefficientTotalTensor.{u, c, v} J R).obj (P, E) ⟶ F :=
    (ordinaryAssociator.{c, v, u} J R F D E).hom ≫ (coefficientTotalTensor.{u, c, v} J R).map
      (X := (F, (coefficientTotalTensor.{u, c, v} J R).obj (D, E)))
      (Y := (F, ringedTensorUnitComplex.{c, v, u} J R)) (𝟙 F, ev) ≫
      (ordinaryRightUnitor.{c, v, u} J R F).hom
  have hc := ordinaryCurry_apply.{c, v, u} J R P E F c n a b (by omega) hb U
    (coefficientTensorGenerator.{u, c, v} J R F D p q n hn U y φ) x
  have hdef : ordinaryEvaluation.{c, v, u} J R E F = ordinaryCurry.{c, v, u} J R P E F c :=
    ordinaryEvaluation_eq.{c, v, u} J R E F
  rw [← hdef] at hc
  change ringedOrdinaryHomValue.{c, v, u} J R E F n a b hb U
      (((ordinaryEvaluation.{c, v, u} J R E F).f n).val.app U
        (coefficientTensorGenerator.{u, c, v} J R F D p q n hn U y φ)) x =
    (c.f b).val.app U (coefficientTensorGenerator.{u, c, v} J R P E n a b
      (by omega) U (coefficientTensorGenerator.{u, c, v} J R F D p q n hn U y φ) x) at hc
  rw [hc]
  have he (r : ℤ) (hr : q + a = r) (hb' : p + r = b) :
      (c.f b).val.app U (coefficientTensorGenerator.{u, c, v} J R P E n a b
        (by omega) U (coefficientTensorGenerator.{u, c, v} J R F D p q n hn U y φ) x) =
      ((ordinaryRightUnitor.{c, v, u} J R F).hom.f b).val.app U
        (coefficientTensorGenerator.{u, c, v} J R F O p r b hb' U y
          ((ev.f r).val.app U
            (coefficientTensorGenerator.{u, c, v} J R D E q a r hr U φ x))) := by
    dsimp only [c]
    simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply]
    rw [ordinaryAssociator_apply.{c, v, u} J R
      F D E p q a n r b hn hr (by omega) hb' U y φ x]
    rw [ordinaryGenerator_map.{c, v, u}]
    rfl
  constructor
  · intro h hp
    cases hp
    rw [he 0 (by omega) (add_zero p)]
    have hv := ordinaryCurry_symm_apply.{c, v, u} J R D E O (𝟙 D) q a 0 (by omega) h U φ x
    change (ev.f 0).val.app U
        (coefficientTensorGenerator.{u, c, v} J R D E q a 0 (by omega) U φ x) =
      ringedOrdinaryHomValue.{c, v, u} J R E O q a 0 h U φ x at hv
    rw [hv]
    have hs :
        ((HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (SheafOfModules.unit ((sheafCompose J
            (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))).inv.val.app U)
          (ringedOrdinaryDualValue.{c, v, u} J R E q a h U φ x) =
        ringedOrdinaryHomValue.{c, v, u} J R E O q a 0 h U φ x := by
      exact congrArg (fun f ↦ f.val.app U
        (ringedOrdinaryHomValue.{c, v, u} J R E O q a 0 h U φ x))
        (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (SheafOfModules.unit ((sheafCompose J
            (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))).hom_inv_id
    rw [← hs]
    exact ordinaryRightUnitor_apply.{c, v, u} J R
      F p (add_zero p) U (ringedOrdinaryDualValue.{c, v, u} J R E q a h U φ x) y
  · intro h
    rw [he (q + a) rfl (by omega)]
    have hz := ordinaryUnit_zero.{c, v, u} J R (q + a) (by omega) U
      ((ev.f (q + a)).val.app U
        (coefficientTensorGenerator.{u, c, v} J R D E q a (q + a) rfl U φ x))
    rw [hz, ordinaryGenerator_zero_right, map_zero]

private theorem ordinaryFormula_ext
    (E F : CochainComplex Mod ℤ)
    (f g : (coefficientTotalTensor.{u, c, v} J R).obj
      (F, homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ⟶
        homComplex (R := R) E F)
    (hf : RingedOrdinaryEvaluationFormula.{c, v, u} J R E F f)
    (hg : RingedOrdinaryEvaluationFormula.{c, v, u} J R E F g) : f = g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply homComplex_hom_ext
  intro a b hab
  apply ordinaryTotalHom_ext.{c, v, u} J R F
    (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) (E.X a) (F.X b) n
  intro p q hpq U y φ x
  change ringedOrdinaryHomValue.{c, v, u} J R E F n a b hab U
      ((f.f n).val.app U
        (coefficientTensorGenerator.{u, c, v} J R F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
          p q n hpq U y φ)) x =
    ringedOrdinaryHomValue.{c, v, u} J R E F n a b hab U
      ((g.f n).val.app U
        (coefficientTensorGenerator.{u, c, v} J R F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
          p q n hpq U y φ)) x
  by_cases h : a + q = 0
  · exact ((hf p q n a b hpq hab U y φ x).1 h (by omega)).trans
      ((hg p q n a b hpq hab U y φ x).1 h (by omega)).symm
  · exact ((hf p q n a b hpq hab U y φ x).2 h).trans
      ((hg p q n a b hpq hab U y φ x).2 h).symm

private theorem ordinaryCurry_pre (P E L F : CochainComplex Mod ℤ)
    (s : L ⟶ E) (g : P ⟶ homComplex (R := R) E F) :
    (ordinaryCurry.{c, v, u} J R P L F).symm
        (g ≫ ((homComplexFunctor (R := R)).map s.op).app F) =
      (coefficientTotalTensor.{u, c, v} J R).map (X := (P, L)) (Y := (P, E))
        (𝟙 P, s) ≫ (ordinaryCurry.{c, v, u} J R P E F).symm g := by
  simpa only [ordinaryCurry, Functor.map_id, Category.id_comp, Category.comp_id] using
    RingedDerivedNative.chainEquiv_symm_naturality.{c, v, u} J R
      P P E L F F (𝟙 P) s (𝟙 F) g

private theorem monoidalEvaluation_pre {D : Type*} [Category D] [MonoidalCategory D]
    (F P E L : D) (s : L ⟶ E) (ev : P ⊗ E ⟶ 𝟙_ D) :
    ((F ⊗ P) ◁ s) ≫ (α_ F P E).hom ≫ (F ◁ ev) ≫ (ρ_ F).hom =
      (α_ F P L).hom ≫ (F ◁ (P ◁ s ≫ ev)) ≫ (ρ_ F).hom := by
  simp only [whiskerLeft_comp, associator_naturality_right_assoc, Category.assoc]

set_option backward.isDefEq.respectTransparency true in
private theorem ordinaryEvaluation_uncurry_pre
    (E F L : CochainComplex Mod ℤ) (s : L ⟶ E) :
    let O := ringedTensorUnitComplex.{c, v, u} J R
    let D := homComplex (R := R) E O
    let P := (coefficientTotalTensor.{u, c, v} J R).obj (F, D)
    let v := (ordinaryCurry.{c, v, u} J R D L O).symm
      (((homComplexFunctor (R := R)).map s.op).app O)
    (ordinaryCurry.{c, v, u} J R P L F).symm
        (ordinaryEvaluation.{c, v, u} J R E F ≫ ((homComplexFunctor (R := R)).map s.op).app F) =
      (ordinaryAssociator.{c, v, u} J R F D L).hom ≫
        (coefficientTotalTensor.{u, c, v} J R).map
          (X := (F, (coefficientTotalTensor.{u, c, v} J R).obj (D, L)))
          (Y := (F, O)) (𝟙 F, v) ≫ (ordinaryRightUnitor.{c, v, u} J R F).hom := by
  let m : MonoidalCategory (CochainComplex Mod ℤ) := inferInstance
  dsimp only
  let O := ringedTensorUnitComplex.{c, v, u} J R
  let D := homComplex (R := R) E O
  let P := (coefficientTotalTensor.{u, c, v} J R).obj (F, D)
  let ev := (ordinaryCurry.{c, v, u} J R D E O).symm (𝟙 D)
  have hv := ordinaryCurry_pre.{c, v, u} J R D E L O s (𝟙 D)
  simp only [Category.id_comp] at hv
  rw [ordinaryCurry_pre.{c, v, u}]
  rw [ordinaryEvaluation_eq]
  rw [Equiv.symm_apply_apply, hv]
  unfold ordinaryAssociator ordinaryRightUnitor
  simp only [RingedDerivedNative.totalTensor_map_eq.{c, v, u} J R]
  simp only [id_tensorHom]
  with_unfolding_all
    exact @monoidalEvaluation_pre (CochainComplex Mod ℤ) inferInstance m F D E L s ev

private theorem ordinaryHomResolution_pre
    (E L G : CochainComplex Mod ℤ) (s : L ⟶ E) :
    DerivedCategory.Q.map (((homComplexFunctor (R := R)).map s.op).app
        ((coefficientHomResolution.{u, c, v} J R).obj G)) ≫
        (coefficientHomResolutionIso.{u, c, v, w} J R L G).inv =
      (coefficientHomResolutionIso.{u, c, v, w} J R E G).inv ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj G)) := by
  simpa only [Functor.map_id, Category.comp_id] using
    (RingedDerivedNative.homRepresentativeIso_inv_naturality.{c, v, u, w}
      J R E L G G s (𝟙 G)).symm

attribute [local irreducible] coefficientHomResolution coefficientHomResolutionIso

private theorem ordinaryHomComparison_pre
    (E L G : CochainComplex Mod ℤ) (s : L ⟶ E) :
    DerivedCategory.Q.map (((homComplexFunctor (R := R)).map s.op).app G) ≫
        ringedOrdinaryHomComparison.{c, v, u, w} J R L G =
      ringedOrdinaryHomComparison.{c, v, u, w} J R E G ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj G)) := by
  unfold ringedOrdinaryHomComparison ringedHomAugmentationMap
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp,
    ← ((homComplexFunctor (R := R)).map s.op).naturality,
    DerivedCategory.Q.map_comp, Category.assoc, ordinaryHomResolution_pre.{c, v, u, w}]
  simp only [Category.assoc]

private theorem ordinaryHomComparison_isIso
    (E G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (h : QuasiIso (ringedHomAugmentationMap.{c, v, u} J R E G)) :
    IsIso (ringedOrdinaryHomComparison.{c, v, u, w} J R E G) := by
  have : IsIso (DerivedCategory.Q.map
      (ringedHomAugmentationMap.{c, v, u} J R E G)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  unfold ringedOrdinaryHomComparison
  infer_instance

private theorem ordinaryCurry_normalize
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (P E F : CochainComplex Mod ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hE : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) E)
    (g : P ⟶ homComplex (R := R) E F) :
    (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj E)
        (DerivedCategory.Q.obj F)).symm
        (DerivedCategory.Q.map g ≫ ringedOrdinaryHomComparison.{c, v, u, w} J R E F) =
      (T.iso J R S P E hP hE).inv ≫
        DerivedCategory.Q.map ((ordinaryCurry.{c, v, u} J R P E F).symm g) := by
  simpa only [ringedOrdinaryHomComparison, ringedHomAugmentationMap,
    Functor.map_comp, Category.assoc] using
    coefficientTensorCurry_normalize.{u, c, v, w} J R S T P E F hP hE
      ((ordinaryCurry.{c, v, u} J R P E F).symm g) g (ordinaryCurry_symm_spec.{c, v, u} J R P E F g)

section DerivedAdjunction

set_option hygiene false in
local notation "Der" => DerivedCategory (RingedTensorModules.{c, v, u} J R)
set_option hygiene false in
local notation "RHom" => derivedInternalHomOfUniverses.{c, v, u, w} J R

variable (S : CoefficientClosedStructure RHom)

private theorem ordinaryTranspose_left {P P' A B : Der} (f : P' ⟶ P)
    (g : S.tensor.obj (P, A) ⟶ B) :
    S.transpose P' A B (S.tensor.map (f, 𝟙 A) ≫ g) =
      f ≫ S.transpose P A B g := by
  let : MonoidalCategory Der := S.monoidal
  dsimp only [CoefficientClosedStructure.transpose,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor]
  rw [tensorHom_id]
  exact (S.adjunction A).homEquiv_naturality_left f g

private theorem ordinaryUntranspose_left {P P' A B : Der} (f : P' ⟶ P)
    (g : P ⟶ (RHom).obj (op A, B)) :
    (S.transpose P' A B).symm (f ≫ g) =
      S.tensor.map (X := (P', A)) (Y := (P, A)) (f, 𝟙 A) ≫
        (S.transpose P A B).symm g := by
  apply (S.transpose P' A B).injective
  rw [Equiv.apply_symm_apply, ordinaryTranspose_left.{c, v, u, w}, Equiv.apply_symm_apply]

private theorem ordinaryTranspose_source (P : Der) {A A' B : Der} (f : A' ⟶ A)
    (g : S.tensor.obj (P, A) ⟶ B) :
    S.transpose P A' B (S.tensor.map (𝟙 P, f) ≫ g) =
      S.transpose P A B g ≫ (RHom).map (f.op, 𝟙 B) := by
  let : MonoidalCategory Der := S.monoidal
  apply (S.transpose P A' B).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = (tensorRight A').map
    (S.transpose P A B g ≫ (RHom).map (f.op, 𝟙 B)) ≫ S.evaluation A' B
  rw [Functor.map_comp, Category.assoc]
  change _ = (S.transpose P A B g ▷ A') ≫
    ((RHom).map (f.op, 𝟙 B) ▷ A') ≫ S.evaluation A' B
  rw [show ((RHom).map (f.op, 𝟙 B) ▷ A') ≫ S.evaluation A' B =
    ((RHom).obj (op A, B) ◁ f) ≫ S.evaluation A B from S.evaluation_naturality A A' B f]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  change _ = (P ◁ f) ≫ (S.transpose P A B).symm (S.transpose P A B g)
  rw [Equiv.symm_apply_apply]
  simp only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom]

private theorem ordinaryDualTensorHom_source
    (unitIso : S.monoidal.tensorUnit ≅
      DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))
    {A A' : Der} (f : A' ⟶ A) (B : Der) :
    S.tensor.map (𝟙 B, (RHom).map (f.op,
        𝟙 (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))) ≫
        ringedDualTensorHom.{c, v, u, w} J R S unitIso A' B =
      ringedDualTensorHom.{c, v, u, w} J R S unitIso A B ≫
        (RHom).map (f.op, 𝟙 B) := by
  let : MonoidalCategory Der := S.monoidal
  unfold ringedDualTensorHom
  rw [← ordinaryTranspose_left.{c, v, u, w}, ← ordinaryTranspose_source.{c, v, u, w}]
  congr 1
  dsimp [CoefficientClosedStructure.tensor]
  simp only [id_tensorHom, tensorHom_id,
    associator_naturality_middle_assoc, associator_naturality_right_assoc]
  have ev := S.evaluation_naturality A A'
    (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)) f
  change ((RHom).map (f.op,
      𝟙 (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) ▷ A') ≫
      S.evaluation A' (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)) =
    ((RHom).obj (op A, DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)) ◁ f) ≫
      S.evaluation A (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)) at ev
  erw [← whiskerLeft_comp_assoc, ev]
  simp only [whiskerLeft_comp, Category.assoc]

private theorem monoidalEvaluation_uncurry {D : Type*} [Category D] [MonoidalCategory D]
    (B P H A O : D) (δ : P ⟶ H) (ev : H ⊗ A ⟶ O) (u : O ⟶ 𝟙_ D) :
    ((𝟙 B ⊗ₘ δ) ⊗ₘ 𝟙 A) ≫ (α_ B H A).hom ≫ B ◁ ev ≫ B ◁ u ≫ (ρ_ B).hom =
      (α_ B P A).hom ≫ (𝟙 B ⊗ₘ ((δ ▷ A) ≫ ev)) ≫
        (𝟙 B ⊗ₘ u) ≫ (ρ_ B).hom := by
  simp only [tensorHom_id, id_tensorHom, associator_naturality_middle_assoc,
    whiskerLeft_comp, Category.assoc]

private theorem ordinaryDualTensorHom_uncurry
    (unitIso : S.monoidal.tensorUnit ≅
      DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))
    (A B P : Der)
    (δ : P ⟶ (RHom).obj
      (op A, DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) :
    (S.transpose (S.tensor.obj (B, P)) A B).symm
        (S.tensor.map (X := (B, P))
          (Y := (B, (RHom).obj
            (op A, DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))))
          (𝟙 B, δ) ≫ ringedDualTensorHom.{c, v, u, w} J R S unitIso A B) =
      (S.monoidal.associator B P A).hom ≫
        S.tensor.map (X := (B, S.tensor.obj (P, A)))
          (Y := (B, DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))
          (𝟙 B, (S.transpose P A
            (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))).symm δ) ≫
        S.tensor.map
          (X := (B, DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))
          (Y := (B, S.monoidal.tensorUnit)) (𝟙 B, unitIso.inv) ≫
        (S.monoidal.rightUnitor B).hom := by
  let : MonoidalCategory Der := S.monoidal
  unfold ringedDualTensorHom
  rw [← ordinaryTranspose_left.{c, v, u, w}, Equiv.symm_apply_apply]
  have hδ : (S.transpose P A
      (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))).symm δ =
      (@MonoidalCategory.tensorRight Der _ S.monoidal A).map δ ≫
        S.evaluation A (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)) :=
    (S.adjunction A).homEquiv_counit P _ δ
  rw [hδ]
  with_unfolding_all
    exact @monoidalEvaluation_uncurry Der inferInstance S.monoidal B P _ A _ δ
      (S.evaluation A (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))
      unitIso.inv

private theorem ordinaryTensorCoherence
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory Der _ S.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (F D L : CochainComplex Mod ℤ)
    (hF : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F)
    (hD : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) D)
    (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    (v : (coefficientTotalTensor.{u, c, v} J R).obj (D, L) ⟶
      ringedTensorUnitComplex.{c, v, u} J R)
    (αord : (coefficientTotalTensor.{u, c, v} J R).obj
        ((coefficientTotalTensor.{u, c, v} J R).obj (F, D), L) ≅
      (coefficientTotalTensor.{u, c, v} J R).obj
        (F, (coefficientTotalTensor.{u, c, v} J R).obj (D, L)))
    (rord : (coefficientTotalTensor.{u, c, v} J R).obj
      (F, ringedTensorUnitComplex.{c, v, u} J R) ≅ F)
    (ha : (coh.tensorIso ((coefficientTotalTensor.{u, c, v} J R).obj (F, D)) L
        (Or.inr hL)).hom ≫ S.tensor.map
          (X := (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (F, D)),
            DerivedCategory.Q.obj L))
          (Y := (S.tensor.obj (DerivedCategory.Q.obj F, DerivedCategory.Q.obj D),
            DerivedCategory.Q.obj L))
          ((T.iso J R S F D hF hD).hom, 𝟙 _) ≫
        (S.monoidal.associator (DerivedCategory.Q.obj F)
          (DerivedCategory.Q.obj D) (DerivedCategory.Q.obj L)).hom =
      DerivedCategory.Q.map αord.hom ≫
        (coh.tensorIso F ((coefficientTotalTensor.{u, c, v} J R).obj (D, L))
          (Or.inl hF)).hom ≫ S.tensor.map
          (X := (DerivedCategory.Q.obj F,
            DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (D, L))))
          (Y := (DerivedCategory.Q.obj F,
            S.tensor.obj (DerivedCategory.Q.obj D, DerivedCategory.Q.obj L)))
          (𝟙 _, (T.iso J R S D L hD hL).hom))
    (hr : (coh.tensorIso F (ringedTensorUnitComplex.{c, v, u} J R) (Or.inl hF)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj F,
            DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))
          (Y := (DerivedCategory.Q.obj F, S.monoidal.tensorUnit)) (𝟙 _, coh.unitIso.inv) ≫
          (S.monoidal.rightUnitor (DerivedCategory.Q.obj F)).hom =
      DerivedCategory.Q.map rord.hom) :
    (coh.tensorIso ((coefficientTotalTensor.{u, c, v} J R).obj (F, D)) L
        (Or.inr hL)).hom ≫ S.tensor.map
          (X := (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (F, D)),
            DerivedCategory.Q.obj L))
          (Y := (S.tensor.obj (DerivedCategory.Q.obj F, DerivedCategory.Q.obj D),
            DerivedCategory.Q.obj L))
          ((T.iso J R S F D hF hD).hom, 𝟙 _) ≫
        (S.monoidal.associator (DerivedCategory.Q.obj F)
          (DerivedCategory.Q.obj D) (DerivedCategory.Q.obj L)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj F,
            S.tensor.obj (DerivedCategory.Q.obj D, DerivedCategory.Q.obj L)))
          (Y := (DerivedCategory.Q.obj F,
            DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))
          (𝟙 _, (T.iso J R S D L hD hL).inv ≫ DerivedCategory.Q.map v) ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj F,
            DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))
          (Y := (DerivedCategory.Q.obj F, S.monoidal.tensorUnit)) (𝟙 _, coh.unitIso.inv) ≫
        (S.monoidal.rightUnitor (DerivedCategory.Q.obj F)).hom =
      DerivedCategory.Q.map (αord.hom ≫
        (coefficientTotalTensor.{u, c, v} J R).map
          (X := (F, (coefficientTotalTensor.{u, c, v} J R).obj (D, L)))
          (Y := (F, ringedTensorUnitComplex.{c, v, u} J R)) (𝟙 F, v) ≫ rord.hom) := by
  rw [reassoc_of% ha, ← Functor.map_comp_assoc]
  simp only [CategoryTheory.prod_comp, Category.id_comp, Iso.hom_inv_id_assoc]
  have hn := coh.tensorIso_naturality F
    ((coefficientTotalTensor.{u, c, v} J R).obj (D, L)) F
    (ringedTensorUnitComplex.{c, v, u} J R) (Or.inl hF) (Or.inl hF) (𝟙 F) v
  simp only [Functor.map_id] at hn
  rw [← reassoc_of% hn, hr, ← DerivedCategory.Q.map_comp,
    ← DerivedCategory.Q.map_comp]

end DerivedAdjunction

private theorem ordinaryMap_comp_naturality {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) {X Y Z : A} {X' Y' : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (γY : Q.obj Y ⟶ X') (γZ : Q.obj Z ⟶ Y')
    (r : X' ⟶ Y') (h : Q.map g ≫ γZ = γY ≫ r) :
    Q.map (f ≫ g) ≫ γZ = Q.map f ≫ γY ≫ r := by
  rw [Q.map_comp, Category.assoc, h]

private theorem ordinaryBifunctor_cancel {D : Type*} [Category D]
    (M : D × D ⥤ D) (X : D) {Y Z W U V V' : D}
    (μ : U ⟶ M.obj (X, Y)) (f : Y ⟶ Z) (g : Z ⟶ W) (k : Y ⟶ W)
    (a : U ⟶ V) (r : V ⟶ V') [Mono r]
    (θ : M.obj (X, Z) ⟶ V) (θ' : M.obj (X, W) ⟶ V')
    (hk : f ≫ g = k) (hθ : M.map (𝟙 X, g) ≫ θ' = θ ≫ r)
    (ha : μ ≫ M.map (𝟙 X, k) ≫ θ' = a ≫ r) :
    μ ≫ M.map (𝟙 X, f) ≫ θ = a := by
  apply (cancel_mono r).1
  simp only [Category.assoc]
  rw [← hθ, ← M.map_comp_assoc]
  simpa only [CategoryTheory.prod_comp, Category.id_comp, hk] using ha

private theorem ordinaryTensor_congr {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (B P A O X : D) (m : X ⟶ S.tensor.obj (S.tensor.obj (B, P), A))
    (δ δ' : S.tensor.obj (P, A) ⟶ O) (u : O ⟶ S.monoidal.tensorUnit)
    (h : δ = δ') :
    m ≫ (S.monoidal.associator B P A).hom ≫
      S.tensor.map (X := (B, S.tensor.obj (P, A))) (Y := (B, O)) (𝟙 B, δ) ≫
      S.tensor.map (X := (B, O)) (Y := (B, S.monoidal.tensorUnit)) (𝟙 B, u) ≫
      (S.monoidal.rightUnitor B).hom =
    m ≫ (S.monoidal.associator B P A).hom ≫
      S.tensor.map (X := (B, S.tensor.obj (P, A))) (Y := (B, O)) (𝟙 B, δ') ≫
      S.tensor.map (X := (B, O)) (Y := (B, S.monoidal.tensorUnit)) (𝟙 B, u) ≫
      (S.monoidal.rightUnitor B).hom := by
  cases h
  rfl

attribute [local irreducible] HomologicalComplex.quasiIso
  HomologicalComplex.instCategory Preadditive.preadditiveHasZeroMorphisms

attribute [local irreducible] CoefficientClosedStructure.tensor
  CoefficientClosedStructure.transpose ringedOrdinaryHomComparison ringedDualTensorHom
  derivedInternalHomOfUniverses CoefficientTensorModels.iso ringedTensorUnitComplex

-- The localized evaluation square needs more time after the upstream bump.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryEvaluation_localizes
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (E F : CochainComplex Mod ℤ)
    (hF : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F)
    (hD : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
      (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))) :
    (T.iso J R S F
        (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) hF hD).hom ≫
      S.tensor.map (X := (DerivedCategory.Q.obj F,
        DerivedCategory.Q.obj (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))))
        (Y := (DerivedCategory.Q.obj F,
          (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
            (op (DerivedCategory.Q.obj E),
              DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))))
        (𝟙 _, ringedOrdinaryHomComparison.{c, v, u, w} J R E
          (ringedTensorUnitComplex.{c, v, u} J R)) ≫
        ringedDualTensorHom.{c, v, u, w} J R S coh.unitIso
          (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F) =
      DerivedCategory.Q.map (ordinaryEvaluation.{c, v, u} J R E F) ≫
        ringedOrdinaryHomComparison.{c, v, u, w} J R E F := by
  classical
  let O := ringedTensorUnitComplex.{c, v, u} J R
  let D := homComplex (R := R) E O
  let P := (coefficientTotalTensor.{u, c, v} J R).obj (F, D)
  obtain ⟨L, s, hL, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max c v u, c, v}
      (C := C) (J := J) (R := R) E
  have hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
      (J := J) (R := R) P :=
    coefficientTotalTensor_isKFlat.{u, c, v} J R F D hF hD
  let u : D ⟶ homComplex (R := R) L O :=
    ((homComplexFunctor (R := R)).map s.op).app O
  let v : (coefficientTotalTensor.{u, c, v} J R).obj (D, L) ⟶ O :=
    (ordinaryCurry.{c, v, u} J R D L O).symm u
  let a : P ⟶ homComplex (R := R) E F := ordinaryEvaluation.{c, v, u} J R E F
  let c : (coefficientTotalTensor.{u, c, v} J R).obj (P, L) ⟶ F :=
    (ordinaryCurry.{c, v, u} J R P L F).symm
    (a ≫ ((homComplexFunctor (R := R)).map s.op).app F)
  have hnO := ordinaryCurry_normalize.{c, v, u, w} J R S T D L O hD hL u
  have hnF := ordinaryCurry_normalize.{c, v, u, w} J R S T P L F hP hL
    (a ≫ ((homComplexFunctor (R := R)).map s.op).app F)
  have hpO := ordinaryHomComparison_pre.{c, v, u, w} J R E L O s
  have hpF := ordinaryHomComparison_pre.{c, v, u, w} J R E L F s
  have harg := ordinaryMap_comp_naturality DerivedCategory.Q a
    (((homComplexFunctor (R := R)).map s.op).app F)
    (ringedOrdinaryHomComparison.{c, v, u, w} J R E F)
    (ringedOrdinaryHomComparison.{c, v, u, w} J R L F)
    ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map
      ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj F))) hpF
  have hnF := (congrArg
    (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj F)).symm harg).symm.trans hnF
  obtain ⟨αord, hα, hαloc⟩ := coh.associator_model F D L hF hD hL
  obtain ⟨rord, hr, hrloc⟩ := coh.rightUnitor_model F hF
  have hαeq := ordinaryAssociator_unique.{c, v, u} J R F D L αord.hom hα
  have hreq := ordinaryRightUnitor_unique.{c, v, u} J R F rord.hom hr
  have hc := ordinaryTensorCoherence.{c, v, u, w} J R S T β coh F D L hF hD hL v
    αord rord hαloc hrloc
  have hc' : c = (ordinaryAssociator.{c, v, u} J R F D L).hom ≫
      (coefficientTotalTensor.{u, c, v} J R).map
        (X := (F, (coefficientTotalTensor.{u, c, v} J R).obj (D, L)))
        (Y := (F, O)) (𝟙 F, v) ≫ (ordinaryRightUnitor.{c, v, u} J R F).hom :=
    ordinaryEvaluation_uncurry_pre.{c, v, u} J R E F L s
  let mid : (coefficientTotalTensor.{u, c, v} J R).obj
      (F, (coefficientTotalTensor.{u, c, v} J R).obj (D, L)) ⟶
      (coefficientTotalTensor.{u, c, v} J R).obj (F, O) :=
    (coefficientTotalTensor.{u, c, v} J R).map
      (X := (F, (coefficientTotalTensor.{u, c, v} J R).obj (D, L)))
      (Y := (F, O)) (𝟙 F, v)
  have hrep := congrArg₂ (fun f g ↦ f ≫ mid ≫ g) hαeq hreq
  have hc := hc.trans (congrArg DerivedCategory.Q.map (hrep.trans hc'.symm))
  let μ := coh.tensorIso P L (Or.inr hL)
  have hμ : μ = T.iso J R S P L hP hL := coh.tensorIso_both P L hP hL
  have hμinv : μ.hom ≫ (T.iso J R S P L hP hL).inv = 𝟙 _ := by
    rw [hμ]
    exact Iso.hom_inv_id _
  have heq : (T.iso J R S F D hF hD).hom ≫
      S.tensor.map (X := (DerivedCategory.Q.obj F, DerivedCategory.Q.obj D))
        (Y := (DerivedCategory.Q.obj F,
          (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
            (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj O)))
        (𝟙 _, DerivedCategory.Q.map u ≫
          ringedOrdinaryHomComparison.{c, v, u, w} J R L O) ≫
      ringedDualTensorHom.{c, v, u, w} J R S coh.unitIso
        (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj F) =
      DerivedCategory.Q.map a ≫ ringedOrdinaryHomComparison.{c, v, u, w} J R E F ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj F)) := by
    apply (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj F)).symm.injective
    apply (cancel_epi μ.hom).1
    rw [ordinaryUntranspose_left.{c, v, u, w}]
    rw [ordinaryDualTensorHom_uncurry.{c, v, u, w}]
    have hO := ordinaryTensor_congr S (DerivedCategory.Q.obj F)
      (DerivedCategory.Q.obj D) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj O)
      (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (P, L)))
      (μ.hom ≫ S.tensor.map
        (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L))
        (Y := (S.tensor.obj (DerivedCategory.Q.obj F, DerivedCategory.Q.obj D),
          DerivedCategory.Q.obj L)) ((T.iso J R S F D hF hD).hom, 𝟙 _))
      ((S.transpose (DerivedCategory.Q.obj D) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj O)).symm
        (DerivedCategory.Q.map u ≫ ringedOrdinaryHomComparison.{c, v, u, w} J R L O))
      ((T.iso J R S D L hD hL).inv ≫ DerivedCategory.Q.map v) coh.unitIso.inv hnO
    simp only [Category.assoc] at hO
    have hFT := congrArg (fun k ↦ μ.hom ≫ k) hnF
    have hcancel : μ.hom ≫ (T.iso J R S P L hP hL).inv ≫
        DerivedCategory.Q.map c = DerivedCategory.Q.map c := by
      rw [← Category.assoc, hμinv, Category.id_comp]
    have hFT := hFT.trans hcancel
    with_unfolding_all
      apply hO.trans
    apply Eq.trans (b := DerivedCategory.Q.map c)
    · simpa only [Category.assoc] using hc
    · exact hFT.symm
  have : QuasiIso s := hs
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hs
  have : IsIso
      (show (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj F) ⟶
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj F) from
        ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj F))) :=
    inferInstanceAs (IsIso (((asIso (DerivedCategory.Q.map s)).op).prod
      (Iso.refl (DerivedCategory.Q.obj F))).hom)
  have : IsIso ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map
      (X := (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj F))
      (Y := (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj F))
      ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj F))) := by infer_instance
  exact ordinaryBifunctor_cancel S.tensor (DerivedCategory.Q.obj F)
    (T.iso J R S F D hF hD).hom
    (ringedOrdinaryHomComparison.{c, v, u, w} J R E O)
    ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map
      (X := (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj O))
      (Y := (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj O))
      ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj O)))
    (DerivedCategory.Q.map u ≫ ringedOrdinaryHomComparison.{c, v, u, w} J R L O)
    (DerivedCategory.Q.map a ≫ ringedOrdinaryHomComparison.{c, v, u, w} J R E F)
    ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map
      (X := (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj F))
      (Y := (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj F))
      ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj F)))
    (ringedDualTensorHom.{c, v, u, w} J R S coh.unitIso
      (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F))
    (ringedDualTensorHom.{c, v, u, w} J R S coh.unitIso
      (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj F)) hpO.symm
    (ordinaryDualTensorHom_source.{c, v, u, w} J R S coh.unitIso
      (DerivedCategory.Q.map s) (DerivedCategory.Q.obj F))
    (by simpa only [Category.assoc] using heq)

end OrdinaryHelpers

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- The ordinary unsigned evaluation exists uniquely and represents derived evaluation
through precisely the two fixed augmentation comparisons.

Source: Stacks Tags 08JD/08JE, 0A98, 08J9 and Section 0A8X
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization).

Proof:
1. Curry ordinary reassociation, tensor with evaluation into the coefficient unit, and
   the right unitor using the proved unsigned chain-level tensor-Hom equivalence.
   Its generator formula gives the stated formula; the unit complex vanishes off zero.
   Generator detection proves uniqueness and identifies the coherence representatives.
2. Naturality of the fixed Hom comparison gives its precomposition identity for every
   s:L→E. Each assumed augmentation quasi-isomorphism makes its own comparison invertible.
3. Choose a K-flat resolution s:L→E. Put D=Hom(E,O), P=Tot(F tensor D), and let v be
   the uncurrying of Hom(s,O). P is K-flat. The two fixed curry normalizations identify
   inverse transposes with the localized maps v and c, where c uncurries a followed
   by Hom(s,F). Ordinary naturality expresses c by reassociation, F tensor v and the unit.
4. Closed-adjunction naturality computes the other inverse transpose using the derived
   associator, tensor with the normalized inverse transpose for O, and the unit constraint.
   The supplied associator, tensor-comparison naturality and right-unitor models identify
   this composite with Q(c), after precomposition with the tensor comparison.
5. Injectivity of inverse transposition and cancellation of the isomorphism H(Qs,1)
   give the square. Only F and D are assumed K-flat, and only the two Hom augmentation
   maps are assumed quasi-isomorphisms; E need not be K-flat or F K-injective. -/
theorem ringedOrdinaryEvaluation_localization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    ∃ aEF : (coefficientTotalTensor.{u, c, v} J R).obj
        (F, homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ⟶
          homComplex (R := R) E F,
      RingedOrdinaryEvaluationFormula.{c, v, u} J R E F aEF ∧
      (∀ bEF, RingedOrdinaryEvaluationFormula.{c, v, u} J R E F bEF → bEF = aEF) ∧
      ∀ (hF : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F)
        (hD : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))),
        QuasiIso (ringedHomAugmentationMap.{c, v, u} J R E
          (ringedTensorUnitComplex.{c, v, u} J R)) →
        QuasiIso (ringedHomAugmentationMap.{c, v, u} J R E F) →
        IsIso (ringedOrdinaryHomComparison.{c, v, u, w} J R E
          (ringedTensorUnitComplex.{c, v, u} J R)) ∧
        IsIso (ringedOrdinaryHomComparison.{c, v, u, w} J R E F) ∧
        (T.iso J R S F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) hF hD).hom ≫
          S.tensor.map (𝟙 (DerivedCategory.Q.obj F),
            ringedOrdinaryHomComparison.{c, v, u, w} J R E
              (ringedTensorUnitComplex.{c, v, u} J R)) ≫
          ringedDualTensorHom.{c, v, u, w} J R S coh.unitIso
            (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F) =
        DerivedCategory.Q.map aEF ≫ ringedOrdinaryHomComparison.{c, v, u, w} J R E F := by
  refine ⟨ordinaryEvaluation.{c, v, u} J R E F,
    ordinaryEvaluation_formula.{c, v, u} J R E F, ?_, ?_⟩
  · intro b hb
    exact ordinaryFormula_ext.{c, v, u} J R E F b (ordinaryEvaluation.{c, v, u} J R E F) hb
      (ordinaryEvaluation_formula.{c, v, u} J R E F)
  · intro hF hD hO hG
    refine ⟨ordinaryHomComparison_isIso.{c, v, u, w} J R E
      (ringedTensorUnitComplex.{c, v, u} J R) hO,
      ordinaryHomComparison_isIso.{c, v, u, w} J R E F hG, ?_⟩
    exact ordinaryEvaluation_localizes.{c, v, u, w} J R S T β coh E F hF hD

end CategoryTheory
