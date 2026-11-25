/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
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
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
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
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Hom-complex composition and the normalized derived adjunction

Source: Stacks Project, sites-cohomology.tex, Tags 0A91 and 0A98, with 08J9
(blueprint: lem-sfb-ringed-hom-composition-model).

The local formula uses the actual Hom-product projections and sheafified tensor
summand generators. The derived comparison uses the fixed augmentation, not an
arbitrary isomorphism between representatives.

## Main declarations

- `ringedHomComposition_existsUnique`: unique sign-free chain composition.
- `ringedHomComposition`: the map determined by that unique characterization.
- `ringedHomRepresentativeMap`: comparison through the fixed augmentation.
- `ringedHomComposition_naturality`: outer naturality and middle dinaturality.
- `ringedHomComposition_model`: agreement with the normalized closed adjunction.
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

/-- The sign-free local homogeneous composition formula, as equality of maps on
all slices. Source: Stacks 0A91, following More on Algebra 0A8I
(blueprint: lem-sfb-ringed-hom-composition-model). -/
def RingedHomCompositionFormula
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (m : (coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F) ⟶ homComplex (R := R) E G) :
    Prop :=
  ∀ (p q k a b : ℤ) (hpq : p + q = k) (hab : a + k = b)
    (hfb : (a + q) + p = b) (U : Cᵒᵖ)
    (f : ((homComplex (R := R) F G).X p).val.obj U)
    (g : ((homComplex (R := R) E F).X q).val.obj U),
    (coefficientHomComponent.{u, c, v} J R E G k a b hab).val.app U
        ((m.f k).val.app U
          (coefficientTensorGenerator.{u, c, v} J R
            (homComplex (R := R) F G) (homComplex (R := R) E F) p q k hpq U f g)) =
      (coefficientHomComponent.{u, c, v} J R E F q a (a + q) rfl).val.app U g ≫
        (coefficientHomComponent.{u, c, v} J R F G p (a + q) b hfb).val.app U f

namespace HomCompositionProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open WeilConjectures.ZeroClassAux

open MonoidalCategory RingedDerivedNative

attribute [local instance 4000] HomologicalComplex.monoidalCategory
attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric
attribute [local irreducible] tensorHomEquiv homComplexFunctor
  PresheafOfModules.sheafificationAdjunction Adjunction.rightAdjointLaxMonoidal
  RingedDerivedNative.chainEquiv

private lemma module_pure_ext
    (M N H : RingedTensorModules.{c, v, u} J R)
    {f g : M ⊗ N ⟶ H}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (CochainPullback.moduleTmul (R := R) M N U x y) =
        g.val.app U (CochainPullback.moduleTmul (R := R) M N U x y)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v u}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private def ev
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj (homComplex (R := R) E F, E) ⟶ F :=
  (RingedDerivedNative.chainEquiv.{c, v, u} J R (homComplex (R := R) E F) E F).symm
    (𝟙 (homComplex (R := R) E F))

attribute [local irreducible] ev

private def comp
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F) ⟶ homComplex (R := R) E G := by
  let : MonoidalClosed (RingedTensorModules.{c, v, u} J R) :=
    RingedDerivedNative.baseClosed.{c, v, u} J R
  let A := homComplex (R := R) F G
  let B := homComplex (R := R) E F
  let W := (coefficientTotalTensor.{u, c, v} J R).obj (A, B)
  exact RingedDerivedNative.chainEquiv.{c, v, u} J R W E G
    ((α_ A B E).hom ≫ (𝟙 A ⊗ₘ ev.{c, v, u} J R E F) ≫ ev.{c, v, u} J R F G)

attribute [local irreducible] comp

private lemma tensor_ext
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P L M : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    {f g : (coefficientTotalTensor.{u, c, v} J R).obj (P, L) ⟶ M}
    (h : ∀ (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (L.X q).val.obj U),
      (f.f k).val.app U (coefficientTensorGenerator.{u, c, v} J R P L p q k hpq U x y) =
        (g.f k).val.app U (coefficientTensorGenerator.{u, c, v} J R P L p q k hpq U x y)) :
    f = g := by
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = k at hpq
  apply module_pure_ext.{c, v, u} J R (P.X p) (L.X q) (M.X k)
  intro U x y
  exact h p q k hpq U x y

private lemma chain_pure
    (P L M : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (φ : P ⟶ homComplex (R := R) L M)
    (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (L.X q).val.obj U) :
    (((RingedDerivedNative.chainEquiv.{c, v, u} J R P L M).symm φ).f k).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P L p q k h U x y) =
      (((φ.f p ≫ homComplexπ L M p q k h').val.app U x).app
        (op (Over.mk (𝟙 U.unop)))).hom y := by
  let := HasDerivedCategory.standard (RingedTensorModules.{c, v, u} J R)
  exact RingedDerivedNative.chainEquiv_symm_pure.{c, v, u, _} J R P L M φ
    p q k h h' U x y

private lemma ev_pure
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
    (f : ((homComplex (R := R) E F).X p).val.obj U) (x : (E.X q).val.obj U) :
    ((ev.{c, v, u} J R E F).f k).val.app U
        (coefficientTensorGenerator.{u, c, v} J R (homComplex (R := R) E F) E
          p q k h U f x) =
      (((coefficientHomComponent.{u, c, v} J R E F p q k h').val.app U f).app
        (op (Over.mk (𝟙 U.unop)))).hom x := by
  simpa only [ev, HomologicalComplex.id_f, Category.id_comp, coefficientHomComponent] using
    chain_pure.{c, v, u} J R _ E F (𝟙 _) p q k h h' U f x

private lemma generator_eq
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    coefficientTensorGenerator.{u, c, v} J R P Q p q k h U x y =
      (HomologicalComplex.ιTensorObj P Q p q k h).val.app U
        (CochainPullback.moduleTmul (R := R) (P.X p) (Q.X q) U x y) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma generator_map
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P P' L L' : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (f : P ⟶ P') (g : L ⟶ L')
    (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (L.X q).val.obj U) :
    (((coefficientTotalTensor.{u, c, v} J R).map (f, g)).f k).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P L p q k h U x y) =
      coefficientTensorGenerator.{u, c, v} J R P' L' p q k h U
        ((f.f p).val.app U x) ((g.f q).val.app U y) := by
  rw [RingedDerivedNative.totalTensor_map_eq.{c, v, u} J R P' P L' L f g]
  have he := HomologicalComplex.ι_mapBifunctorMap f g
    (curriedTensor (RingedTensorModules.{c, v, u} J R)) (.up ℤ) p q k h
  change HomologicalComplex.ιTensorObj P L p q k h ≫
      (f ⊗ₘ g).f k =
    (f.f p ▷ L.X q) ≫ (P'.X p ◁ g.f q) ≫
      HomologicalComplex.ιTensorObj P' L' p q k h at he
  rw [← Category.assoc, ← tensorHom_def] at he
  have he' := congrArg (fun z ↦ z.val.app U
    (CochainPullback.moduleTmul (R := R) (P.X p) (L.X q) U x y)) he
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    CochainPullback.moduleTmul_map (R := R)] at he'
  simp only [generator_eq]
  convert he' using 0

private lemma generator_restrict
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P L : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (p q k : ℤ) (h : p + q = k) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (L.X q).val.obj U) :
    (((coefficientTotalTensor.{u, c, v} J R).obj (P, L)).X k).val.map i
        (coefficientTensorGenerator.{u, c, v} J R P L p q k h U x y) =
      coefficientTensorGenerator.{u, c, v} J R P L p q k h V
        ((P.X p).val.map i x) ((L.X q).val.map i y) := by
  have hi := PresheafOfModules.naturality_apply
    (HomologicalComplex.ιTensorObj P L p q k h).val i
    (CochainPullback.moduleTmul (R := R) (P.X p) (L.X q) U x y)
  change _ = (HomologicalComplex.ιTensorObj P L p q k h).val.app V
    (CochainPullback.moduleTmul (R := R) (P.X p) (L.X q) V
      ((P.X p).val.map i x) ((L.X q).val.map i y))
  erw [← hi]
  exact congrArg ((HomologicalComplex.ιTensorObj P L p q k h).val.app V)
    (CochainPullback.moduleTmul_restrict (R := R) (P.X p) (L.X q) i x y)

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
private lemma component_restrict_eval
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (n a b : ℤ) (h : a + n = b) {U : Cᵒᵖ} {V : C} (i : V ⟶ U.unop)
    (z : ((homComplex (R := R) E F).X n).val.obj U) (x : (E.X a).val.obj (op V)) :
    (((coefficientHomComponent.{u, c, v} J R E F n a b h).val.app (op V)
        (((homComplex (R := R) E F).X n).val.map i.op z)).app
          (op (Over.mk (𝟙 V)))).hom x =
      (((coefficientHomComponent.{u, c, v} J R E F n a b h).val.app U z).app
        (op (Over.mk i))).hom x := by
  rw [PresheafOfModules.naturality_apply]
  change ((PresheafOfModules.restrictOverMap i
    ((coefficientHomComponent.{u, c, v} J R E F n a b h).val.app U z)).app
      (op (Over.mk (𝟙 V)))).hom x = _
  change (((coefficientHomComponent.{u, c, v} J R E F n a b h).val.app U z).app
    (op (Over.mk ((𝟙 V) ≫ i)))).hom x =
    (((coefficientHomComponent.{u, c, v} J R E F n a b h).val.app U z).app
      (op (Over.mk i))).hom x
  exact congrArg (fun j : V ⟶ U.unop ↦
    (show (F.X b).val.obj (op V) from
      (((coefficientHomComponent.{u, c, v} J R E F n a b h).val.app U z).app
        (op (Over.mk j))).hom x)) (Category.id_comp i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma triple_tensor_ext
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P Q L M : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    {f g : (coefficientTotalTensor.{u, c, v} J R).obj
      ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q), L) ⟶ M}
    (h : ∀ (p q r n : ℤ) (hn : (p + q) + r = n) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (L.X r).val.obj U),
      (f.f n).val.app U (coefficientTensorGenerator.{u, c, v} J R
        ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L
        (p + q) r n hn U (coefficientTensorGenerator.{u, c, v} J R
          P Q p q (p + q) rfl U x y) z) =
      (g.f n).val.app U (coefficientTensorGenerator.{u, c, v} J R
        ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L
        (p + q) r n hn U (coefficientTensorGenerator.{u, c, v} J R
          P Q p q (p + q) rfl U x y) z)) : f = g := by
  let φ := RingedDerivedNative.chainEquiv.{c, v, u} J R
    ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L M f
  let ψ := RingedDerivedNative.chainEquiv.{c, v, u} J R
    ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L M g
  apply (RingedDerivedNative.chainEquiv.{c, v, u} J R
    ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) L M).injective
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = k at hpq
  apply homComplex_hom_ext.{c, v, max c v u, max c v u} (R := R)
  intro a b hab
  apply module_pure_ext.{c, v, u} J R (P.X p) (Q.X q)
    (SheafOfModules.homObj (R := R) (L.X a) (M.X b))
  intro U x y
  apply PresheafOfModules.hom_ext
  intro W
  ext z
  with_unfolding_all change
    (((coefficientHomComponent.{u, c, v} J R L M k a b hab).val.app U
      ((φ.f k).val.app U (coefficientTensorGenerator.{u, c, v} J R
        P Q p q k hpq U x y))).app W).hom z =
    (((coefficientHomComponent.{u, c, v} J R L M k a b hab).val.app U
      ((ψ.f k).val.app U (coefficientTensorGenerator.{u, c, v} J R
        P Q p q k hpq U x y))).app W).hom z
  erw [← component_restrict_eval.{c, v, u} J R L M k a b hab W.unop.hom,
    ← component_restrict_eval.{c, v, u} J R L M k a b hab W.unop.hom]
  erw [← PresheafOfModules.naturality_apply (φ.f k).val W.unop.hom.op,
    ← PresheafOfModules.naturality_apply (ψ.f k).val W.unop.hom.op]
  erw [generator_restrict.{c, v, u} J R P Q p q k hpq W.unop.hom.op]
  have hf := chain_pure.{c, v, u} J R _ L M φ k a b (by omega) hab
    (op W.unop.left)
    (coefficientTensorGenerator.{u, c, v} J R P Q p q k hpq (op W.unop.left)
      ((P.X p).val.map W.unop.hom.op x) ((Q.X q).val.map W.unop.hom.op y)) z
  have hg := chain_pure.{c, v, u} J R _ L M ψ k a b (by omega) hab
    (op W.unop.left)
    (coefficientTensorGenerator.{u, c, v} J R P Q p q k hpq (op W.unop.left)
      ((P.X p).val.map W.unop.hom.op x) ((Q.X q).val.map W.unop.hom.op y)) z
  simp only [φ, ψ, Equiv.symm_apply_apply] at hf hg
  have hx := h p q a b (by omega) (op W.unop.left)
    ((P.X p).val.map W.unop.hom.op x) ((Q.X q).val.map W.unop.hom.op y) z
  have hk : k = p + q := hpq.symm
  subst k
  exact hf.symm.trans (hx.trans hg)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma comp_eval_pure
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (p q k a b : ℤ) (hpq : p + q = k) (hab : a + k = b)
    (hfb : (a + q) + p = b) (U : Cᵒᵖ)
    (f : ((homComplex (R := R) F G).X p).val.obj U)
    (g : ((homComplex (R := R) E F).X q).val.obj U)
    (x : (E.X a).val.obj U) :
    (((coefficientHomComponent.{u, c, v} J R E G k a b hab).val.app U
        (((comp.{c, v, u} J R E F G).f k).val.app U
          (coefficientTensorGenerator.{u, c, v} J R
            (homComplex (R := R) F G) (homComplex (R := R) E F)
            p q k hpq U f g))).app (op (Over.mk (𝟙 U.unop)))).hom x =
      (((coefficientHomComponent.{u, c, v} J R F G p (a + q) b hfb).val.app U f).app
        (op (Over.mk (𝟙 U.unop)))).hom
          ((((coefficientHomComponent.{u, c, v} J R E F q a (a + q) rfl).val.app U g).app
            (op (Over.mk (𝟙 U.unop)))).hom x) := by
  have he := chain_pure.{c, v, u} J R
    ((coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F)) E G
    (comp.{c, v, u} J R E F G) k a b (by omega) hab U
    (coefficientTensorGenerator.{u, c, v} J R
      (homComplex (R := R) F G) (homComplex (R := R) E F) p q k hpq U f g) x
  dsimp only [coefficientHomComponent]
  erw [← he]
  have hcomp : comp.{c, v, u} J R E F G =
      RingedDerivedNative.chainEquiv.{c, v, u} J R
        ((coefficientTotalTensor.{u, c, v} J R).obj
          (homComplex (R := R) F G, homComplex (R := R) E F)) E G
        ((α_ (homComplex (R := R) F G) (homComplex (R := R) E F) E).hom ≫
          (𝟙 _ ⊗ₘ ev.{c, v, u} J R E F) ≫ ev.{c, v, u} J R F G) := by
    simp only [comp]
  rw [hcomp, Equiv.symm_apply_apply]
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [(RingedDerivedNative.complexConstraints.{c, v, u} J R).associator
    (homComplex (R := R) F G) (homComplex (R := R) E F) E
    p q a k (a + q) b hpq (by omega) (by omega) (by omega) U f g x]
  rw [← RingedDerivedNative.totalTensor_map_eq.{c, v, u} J R
    (homComplex (R := R) F G) (homComplex (R := R) F G) F
    ((coefficientTotalTensor.{u, c, v} J R).obj (homComplex (R := R) E F, E))
    (𝟙 _) (ev.{c, v, u} J R E F)]
  erw [generator_map.{c, v, u} J R]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  erw [ev_pure.{c, v, u} J R E F q a (a + q) (by omega) rfl,
    ev_pure.{c, v, u} J R F G p (a + q) b (by omega) hfb]
  rfl

private lemma comp_formula
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    RingedHomCompositionFormula.{c, v, u} J R E F G (comp.{c, v, u} J R E F G) := by
  intro p q k a b hpq hab hfb U f g
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  let i := W.unop.hom
  have he := comp_eval_pure.{c, v, u} J R E F G p q k a b hpq hab hfb (op W.unop.left)
    (((homComplex (R := R) F G).X p).val.map i.op f)
    (((homComplex (R := R) E F).X q).val.map i.op g) x
  erw [← generator_restrict.{c, v, u} J R] at he
  erw [PresheafOfModules.naturality_apply ((comp.{c, v, u} J R E F G).f k).val i.op]
    at he
  erw [component_restrict_eval.{c, v, u} J R,
    component_restrict_eval.{c, v, u} J R, component_restrict_eval.{c, v, u} J R] at he
  exact he

private lemma formula_unique
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (m n : (coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F) ⟶ homComplex (R := R) E G)
    (hm : RingedHomCompositionFormula.{c, v, u} J R E F G m)
    (hn : RingedHomCompositionFormula.{c, v, u} J R E F G n) : m = n := by
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = k at hpq
  apply homComplex_hom_ext.{c, v, max c v u, max c v u} (R := R)
  intro a b hab
  change ((HomologicalComplex.ιTensorObj (homComplex (R := R) F G)
      (homComplex (R := R) E F) p q k hpq ≫ m.f k) ≫ homComplexπ E G k a b hab) =
    ((HomologicalComplex.ιTensorObj (homComplex (R := R) F G)
      (homComplex (R := R) E F) p q k hpq ≫ n.f k) ≫ homComplexπ E G k a b hab)
  apply module_pure_ext.{c, v, u} J R
    ((homComplex (R := R) F G).X p) ((homComplex (R := R) E F).X q)
      (SheafOfModules.homObj (R := R) (E.X a) (G.X b))
  intro U f g
  exact (hm p q k a b hpq hab (by omega) U f g).trans
    (hn p q k a b hpq hab (by omega) U f g).symm

end HomCompositionProof

/-- There is exactly one chain map with the specified homogeneous composition formula.
Source: Stacks 0A91 and More on Algebra 0A8I
(blueprint: lem-sfb-ringed-hom-composition-model).
Proof: use the sign-free chain tensor-Hom equivalence. Evaluation is the inverse
transpose of the identity, and composition is the transpose of two evaluations
and the native associator. These constructions already give chain maps. Their
homogeneous pure-section formulas give f(g(x)); restriction naturality gives the
formula on every slice. The total-tensor summand inclusions, Hom-product projections,
and sheaf-tensor universal property prove uniqueness. No infinite sum of Hom-product
coordinates is used. -/
theorem ringedHomComposition_existsUnique
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    ∃! m : (coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F) ⟶ homComplex (R := R) E G,
      RingedHomCompositionFormula.{c, v, u} J R E F G m := by
  let : HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R) :=
    RingedDerivedNative.baseLimits.{c, v, u} J R
  let : HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R) :=
    RingedDerivedNative.baseColimits.{c, v, u} J R
  let : ∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y :=
    RingedDerivedNative.gradedTensor.{c, v, u} J R
  let : ∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
      GradedObject.HasTensor₄ObjExt W X Y Z :=
    RingedDerivedNative.gradedTensorFour.{c, v, u} J R
  let : ∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    RingedDerivedNative.gradedTensorLeft.{c, v, u} J R
  let : ∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    RingedDerivedNative.gradedTensorRight.{c, v, u} J R
  refine ⟨HomCompositionProof.comp.{c, v, u} J R E F G,
    HomCompositionProof.comp_formula.{c, v, u} J R E F G, ?_⟩
  intro m hm
  exact HomCompositionProof.formula_unique.{c, v, u} J R E F G m _ hm
    (HomCompositionProof.comp_formula.{c, v, u} J R E F G)

/-- The actual Hom-complex composition, determined uniquely by its local formula.
Source: Stacks 0A91 (blueprint: lem-sfb-ringed-hom-composition-model). -/
def ringedHomComposition
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F) ⟶ homComplex (R := R) E G :=
  (ringedHomComposition_existsUnique.{c, v, u} J R E F G).exists.choose

/-- The fixed augmentation used by the recorded derived Hom construction.
Source: Stacks 079P, 0A95 (blueprint: lem-sfb-ringed-hom-composition-model). -/
def ringedHomAugmentation
    (F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    F ⟶ (coefficientHomResolution.{u, c, v} J R).obj F :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J R).1
  (CochainComplex.toKInjectiveResolution.{max c v u} _).app F

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- Canonical comparison from a Hom representative to the fixed derived internal Hom.
It is an isomorphism for a K-injective target: postcompose by its fixed augmentation,
then invert the recorded localization-factorization comparison.
Source: Stacks 0A95, 0A98 (blueprint: lem-sfb-ringed-hom-composition-model). -/
def ringedHomRepresentativeMap
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    DerivedCategory.Q.obj (homComplex (R := R) E F) ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj F) :=
  DerivedCategory.Q.map
      (((homComplexFunctor (R := R)).obj (op E)).map
        (ringedHomAugmentation.{c, v, u} J R F)) ≫
    (coefficientHomResolutionIso.{u, c, v, w} J R E F).inv

namespace HomCompositionProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

open WeilConjectures.ZeroClassAux

attribute [local instance 4000] HomologicalComplex.monoidalCategory
attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric
attribute [local irreducible] tensorHomEquiv homComplexFunctor homComplexπ
  SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction Adjunction.rightAdjointLaxMonoidal
  RingedDerivedNative.chainEquiv

attribute [local irreducible] ringedHomComposition

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma composition_formula
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    RingedHomCompositionFormula.{c, v, u} J R E F G
      (ringedHomComposition.{c, v, u} J R E F G) := by
  unfold ringedHomComposition
  exact (ringedHomComposition_existsUnique.{c, v, u} J R E F G).exists.choose_spec

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma pre_eval
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E P F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (s : P ⟶ E) (n a b : ℤ) (h : a + n = b) (U : Cᵒᵖ)
    (z : ((homComplex (R := R) E F).X n).val.obj U) (x : (P.X a).val.obj U) :
    (((coefficientHomComponent.{u, c, v} J R P F n a b h).val.app U
        (((((homComplexFunctor (R := R)).map s.op).app F).f n).val.app U z)).app
          (op (Over.mk (𝟙 U.unop)))).hom x =
      (((coefficientHomComponent.{u, c, v} J R E F n a b h).val.app U z).app
        (op (Over.mk (𝟙 U.unop)))).hom ((s.f a).val.app U x) := by
  have he := homComplexFunctor_map_f_π s (𝟙 F) n a b h
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at he
  have he' := congrArg (fun f ↦ (f.val.app U z).app (op (Over.mk (𝟙 U.unop))) x) he
  exact he'

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma pre_component
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E P F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (s : P ⟶ E) (n a b : ℤ) (h : a + n = b) :
    ((((homComplexFunctor (R := R)).map s.op).app F).f n) ≫
        homComplexπ P F n a b h =
      homComplexπ E F n a b h ≫ SheafOfModules.homObjMap (R := R) (s.f a) (𝟙 (F.X b)) := by
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using
    homComplexFunctor_map_f_π s (𝟙 F) n a b h

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma composition_mapped_formula
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P T U F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (f : U ⟶ homComplex (R := R) F G) (g : T ⟶ homComplex (R := R) P F)
    (p q k a b : ℤ) (hpq : p + q = k) (hab : a + k = b)
    (hfb : (a + q) + p = b) (V : Cᵒᵖ)
    (x : (U.X p).val.obj V) (y : (T.X q).val.obj V) :
    (coefficientHomComponent.{u, c, v} J R P G k a b hab).val.app V
        ((((coefficientTotalTensor.{u, c, v} J R).map (f, g) ≫
          ringedHomComposition.{c, v, u} J R P F G).f k).val.app V
            (coefficientTensorGenerator.{u, c, v} J R U T p q k hpq V x y)) =
      (coefficientHomComponent.{u, c, v} J R P F q a (a + q) rfl).val.app V
          ((g.f q).val.app V y) ≫
        (coefficientHomComponent.{u, c, v} J R F G p (a + q) b hfb).val.app V
          ((f.f p).val.app V x) := by
  have hm := generator_map.{c, v, u} J R U (homComplex (R := R) F G)
    T (homComplex (R := R) P F) f g p q k hpq V x y
  have hc := composition_formula.{c, v, u} J R P F G p q k a b hpq hab hfb V
    ((f.f p).val.app V x) ((g.f q).val.app V y)
  have he := congrArg (fun z ↦
    (coefficientHomComponent.{u, c, v} J R P G k a b hab).val.app V
      (((ringedHomComposition.{c, v, u} J R P F G).f k).val.app V z)) hm
  convert he.trans hc using 0
  rfl

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
set_option backward.isDefEq.respectTransparency.types true in
private lemma composition_source
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E P F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (s : P ⟶ E) :
    ringedHomComposition.{c, v, u} J R E F G ≫
        ((homComplexFunctor (R := R)).map s.op).app G =
      (coefficientTotalTensor.{u, c, v} J R).map
        (𝟙 (homComplex (R := R) F G), ((homComplexFunctor (R := R)).map s.op).app F) ≫
          ringedHomComposition.{c, v, u} J R P F G := by
  with_unfolding_all
    let preF : homComplex (R := R) E F ⟶ homComplex (R := R) P F :=
      ((homComplexFunctor (R := R)).map s.op).app F
    let preG : homComplex (R := R) E G ⟶ homComplex (R := R) P G :=
      ((homComplexFunctor (R := R)).map s.op).app G
    change ringedHomComposition.{c, v, u} J R E F G ≫ preG =
      (coefficientTotalTensor.{u, c, v} J R).map
        (X := (homComplex (R := R) F G, homComplex (R := R) E F))
        (Y := (homComplex (R := R) F G, homComplex (R := R) P F)) (𝟙 _, preF) ≫
      ringedHomComposition.{c, v, u} J R P F G
    ext k : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = k at hpq
    apply homComplex_hom_ext.{c, v, max c v u, max c v u} (R := R)
    intro a b hab
    change ((HomologicalComplex.ιTensorObj (homComplex (R := R) F G)
        (homComplex (R := R) E F) p q k hpq ≫
          (ringedHomComposition.{c, v, u} J R E F G ≫ preG).f k) ≫
            homComplexπ P G k a b hab) =
      ((HomologicalComplex.ιTensorObj (homComplex (R := R) F G)
        (homComplex (R := R) E F) p q k hpq ≫
          ((coefficientTotalTensor.{u, c, v} J R).map
            (X := (homComplex (R := R) F G, homComplex (R := R) E F))
            (Y := (homComplex (R := R) F G, homComplex (R := R) P F))
            (𝟙 _, preF) ≫ ringedHomComposition.{c, v, u} J R P F G).f k) ≫
              homComplexπ P G k a b hab)
    apply module_pure_ext.{c, v, u} J R
      ((homComplex (R := R) F G).X p) ((homComplex (R := R) E F).X q)
        (SheafOfModules.homObj (R := R) (P.X a) (G.X b))
    intro V f g
    change (coefficientHomComponent.{u, c, v} J R P G k a b hab).val.app V
        ((preG.f k).val.app V
          (((ringedHomComposition.{c, v, u} J R E F G).f k).val.app V
            (coefficientTensorGenerator.{u, c, v} J R
              (homComplex (R := R) F G) (homComplex (R := R) E F)
              p q k hpq V f g))) =
      (coefficientHomComponent.{u, c, v} J R P G k a b hab).val.app V
        ((((coefficientTotalTensor.{u, c, v} J R).map
          (X := (homComplex (R := R) F G, homComplex (R := R) E F))
          (Y := (homComplex (R := R) F G, homComplex (R := R) P F)) (𝟙 _, preF) ≫
          ringedHomComposition.{c, v, u} J R P F G).f k).val.app V
            (coefficientTensorGenerator.{u, c, v} J R
              (homComplex (R := R) F G) (homComplex (R := R) E F)
              p q k hpq V f g))
    have hp := congrArg (fun z ↦ z.val.app V
      (((ringedHomComposition.{c, v, u} J R E F G).f k).val.app V
        (coefficientTensorGenerator.{u, c, v} J R
          (homComplex (R := R) F G) (homComplex (R := R) E F)
          p q k hpq V f g)))
      (pre_component.{c, v, u} J R E P G s k a b hab)
    change (coefficientHomComponent.{u, c, v} J R P G k a b hab).val.app V
        ((preG.f k).val.app V _) =
      (SheafOfModules.homObjMap (R := R) (s.f a) (𝟙 (G.X b))).val.app V
        ((coefficientHomComponent.{u, c, v} J R E G k a b hab).val.app V _) at hp
    erw [hp]
    erw [composition_formula.{c, v, u} J R E F G p q k a b hpq hab (by omega) V f g]
    erw [composition_mapped_formula.{c, v, u} J R P
      (homComplex (R := R) E F) (homComplex (R := R) F G) F G
      (𝟙 _) preF p q k a b hpq hab (by omega) V f g]
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply]
    have he := congrArg (fun z ↦ z.val.app V g)
      (pre_component.{c, v, u} J R E P F s q a (a + q) rfl)
    change (coefficientHomComponent.{u, c, v} J R P F q a (a + q) rfl).val.app V
        (((((homComplexFunctor (R := R)).map s.op).app F).f q).val.app V g) =
      (SheafOfModules.homObjMap (R := R) (s.f a) (𝟙 (F.X (a + q)))).val.app V
        ((coefficientHomComponent.{u, c, v} J R E F q a (a + q) rfl).val.app V g) at he
    erw [he]
    rfl

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
set_option backward.isDefEq.respectTransparency.types true in
private lemma triple_uncurry
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P T U F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (f : U ⟶ homComplex (R := R) F G) (g : T ⟶ homComplex (R := R) P F)
    (a : (coefficientTotalTensor.{u, c, v} J R).obj
        ((coefficientTotalTensor.{u, c, v} J R).obj (U, T), P) ⟶
      (coefficientTotalTensor.{u, c, v} J R).obj
        (U, (coefficientTotalTensor.{u, c, v} J R).obj (T, P)))
    (ha : ∀ (p q r n : ℤ) (hn : (p + q) + r = n) (V : Cᵒᵖ)
      (x : (U.X p).val.obj V) (y : (T.X q).val.obj V) (z : (P.X r).val.obj V),
      (a.f n).val.app V (coefficientTensorGenerator.{u, c, v} J R
        ((coefficientTotalTensor.{u, c, v} J R).obj (U, T)) P
        (p + q) r n hn V (coefficientTensorGenerator.{u, c, v} J R
          U T p q (p + q) rfl V x y) z) =
      coefficientTensorGenerator.{u, c, v} J R U
        ((coefficientTotalTensor.{u, c, v} J R).obj (T, P))
        p (r + q) n (by omega) V x
        (coefficientTensorGenerator.{u, c, v} J R T P q r (r + q) (by omega) V y z)) :
    (RingedDerivedNative.chainEquiv.{c, v, u} J R
      ((coefficientTotalTensor.{u, c, v} J R).obj (U, T)) P G).symm
        ((coefficientTotalTensor.{u, c, v} J R).map (f, g) ≫
          ringedHomComposition.{c, v, u} J R P F G) =
      a ≫ (RingedDerivedNative.chainEquiv.{c, v, u} J R U
        ((coefficientTotalTensor.{u, c, v} J R).obj (T, P)) G).symm
          (f ≫ ((homComplexFunctor (R := R)).map
            ((RingedDerivedNative.chainEquiv.{c, v, u} J R T P F).symm g).op).app G) := by
  apply triple_tensor_ext.{c, v, u} J R U T P G
  intro p q r n hn V x y z
  erw [chain_pure.{c, v, u} J R _ P G _
    (p + q) r n hn (by omega)]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hf := composition_mapped_formula.{c, v, u} J R P T U F G f g
    p q (p + q) r n rfl (by omega) (by omega) V x y
  dsimp only [coefficientHomComponent] at hf
  erw [hf]
  erw [HomologicalComplex.comp_f]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [ha, chain_pure.{c, v, u} J R U _ G _
    p (r + q) n (by omega) (by omega)]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [pre_eval.{c, v, u} J R, chain_pure.{c, v, u} J R
    T P F g q r (r + q) (by omega) rfl]
  rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

private lemma representative_source
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (E P F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) (s : P ⟶ E) :
    ringedHomRepresentativeMap.{c, v, u, w} J R E F ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj F)) =
      DerivedCategory.Q.map (((homComplexFunctor (R := R)).map s.op).app F) ≫
        ringedHomRepresentativeMap.{c, v, u, w} J R P F := by
  with_unfolding_all
    unfold ringedHomRepresentativeMap
    erw [Category.assoc]
    have hn := RingedDerivedNative.homRepresentativeIso_inv_naturality.{c, v, u, w}
      J R E P F F s (𝟙 F)
    simp only [Functor.map_id] at hn
    erw [hn]
    simp only [Category.comp_id]
    erw [← Category.assoc, ← DerivedCategory.Q.map_comp,
      ← Category.assoc, ← DerivedCategory.Q.map_comp]
    congr 2
    exact (((homComplexFunctor (R := R)).map s.op).naturality
      (ringedHomAugmentation.{c, v, u} J R F))

private lemma normalized_uncurry
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (N : CoefficientTensorModels.{u, c, v, w} J R S)
    (P L M : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    (φ : P ⟶ homComplex (R := R) L M) :
    (N.iso J R S P L hP hL).hom ≫
        (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M)).symm
            (DerivedCategory.Q.map φ ≫ ringedHomRepresentativeMap.{c, v, u, w} J R L M) =
      DerivedCategory.Q.map ((RingedDerivedNative.chainEquiv.{c, v, u} J R P L M).symm φ) := by
  with_unfolding_all
    let η := ringedHomAugmentation.{c, v, u} J R M
    let φI := φ ≫ ((homComplexFunctor (R := R)).obj (op L)).map η
    obtain ⟨ψ, hψpure, hψ⟩ := N.uncurry_model ⟨P, hP⟩ ⟨L, hL⟩ M φI
    have hψeq : ψ = (RingedDerivedNative.chainEquiv.{c, v, u} J R P L
        ((coefficientHomResolution.{u, c, v} J R).obj M)).symm φI := by
      apply tensor_ext.{c, v, u} J R P L _
      intro p q k h U x y
      exact (hψpure p q k h (by omega) U x y).trans
        (chain_pure.{c, v, u} J R P L _ φI
          p q k h (by omega) U x y).symm
    have hunc : (RingedDerivedNative.chainEquiv.{c, v, u} J R P L
        ((coefficientHomResolution.{u, c, v} J R).obj M)).symm φI =
        (RingedDerivedNative.chainEquiv.{c, v, u} J R P L M).symm φ ≫ η := by
      have hn := RingedDerivedNative.chainEquiv_symm_naturality.{c, v, u} J R
        P P L L M _ (𝟙 P) (𝟙 L) η φ
      have htensor : (coefficientTotalTensor.{u, c, v} J R).map
          (X := (P, L)) (Y := (P, L)) (𝟙 P, 𝟙 L) = 𝟙 _ :=
        (coefficientTotalTensor.{u, c, v} J R).map_id (P, L)
      rw [htensor] at hn
      simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] at hn
      erw [Category.id_comp] at hn
      dsimp only [φI]
      convert hn using 0
      rfl
    have hη : DerivedCategory.Q.{w}.map η ≫
        coefficientHomResolutionInverse.{u, c, v, w} J R M = 𝟙 _ := by
      exact (RingedDerivedNative.augmentationIso.{c, v, u, w} J R M).hom_inv_id
    erw [hψeq, hunc] at hψ
    simp only [Functor.map_comp, Category.assoc, hη, Category.comp_id] at hψ
    dsimp only [φI] at hψ
    erw [Functor.map_comp] at hψ
    simp only [ringedHomRepresentativeMap, CoefficientTensorModels.iso, Iso.app_hom]
    convert hψ using 0
    simp only [Category.assoc, η]
    rfl

end HomCompositionProof

private lemma closed_uncurry_composition
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (K L M : A) :
    (S.transpose _ K M).symm (S.composition K L M) =
      (S.monoidal.associator (H.obj (op L, M)) (H.obj (op K, L)) K).hom ≫
        S.tensor.map
          (X := (H.obj (op L, M), S.tensor.obj (H.obj (op K, L), K)))
          (Y := (H.obj (op L, M), L)) (𝟙 _, S.evaluation K L) ≫ S.evaluation L M := by
  exact (S.transpose _ K M).symm_apply_apply _

private lemma closed_uncurry
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (X K M : A) (f : X ⟶ H.obj (op K, M)) :
    (S.transpose X K M).symm f = S.tensor.map (f, 𝟙 K) ≫ S.evaluation K M := by
  let := S.monoidal
  change ((S.adjunction K).homEquiv X M).symm f = _
  erw [Adjunction.homEquiv_symm_apply]
  simp only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id]
  rfl

private lemma closed_eval_source
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (K K' M : A) (a : K' ⟶ K) :
    S.tensor.map (X := (H.obj (op K, M), K'))
        (Y := (H.obj (op K', M), K')) (H.map (a.op, 𝟙 M), 𝟙 K') ≫
        S.evaluation K' M =
      S.tensor.map (X := (H.obj (op K, M), K'))
        (Y := (H.obj (op K, M), K)) (𝟙 (H.obj (op K, M)), a) ≫ S.evaluation K M := by
  let := S.monoidal
  simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorRight, MonoidalCategory.tensorLeft,
    Functor.flip, MonoidalCategory.curriedTensor, MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom] using S.evaluation_naturality K K' M a

private lemma closed_uncurry_source
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (X K K' M : A) (a : K' ⟶ K)
    (f : X ⟶ H.obj (op K, M)) :
    (S.transpose X K' M).symm (f ≫ H.map (a.op, 𝟙 M)) =
      S.tensor.map (𝟙 X, a) ≫ (S.transpose X K M).symm f := by
  rw [closed_uncurry, closed_uncurry]
  have h := congrArg (fun k : S.tensor.obj (H.obj (op K, M), K') ⟶ M ↦
    S.tensor.map (X := (X, K')) (Y := (H.obj (op K, M), K')) (f, 𝟙 K') ≫ k)
    (closed_eval_source S K K' M a)
  simpa only [← Category.assoc, ← S.tensor.map_comp, prod_comp,
    Category.id_comp, Category.comp_id] using h

private lemma closed_uncurry_precomp
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (X X' K M : A) (a : X' ⟶ X)
    (f : X ⟶ H.obj (op K, M)) :
    (S.transpose X' K M).symm (a ≫ f) =
      S.tensor.map (a, 𝟙 K) ≫ (S.transpose X K M).symm f := by
  rw [closed_uncurry, closed_uncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp, prod_comp,
    Category.id_comp]

private lemma closed_uncurry_postcomp
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (X K M M' : A) (b : M ⟶ M')
    (f : X ⟶ H.obj (op K, M)) :
    (S.transpose X K M').symm (f ≫ H.map (𝟙 (op K), b)) =
      (S.transpose X K M).symm f ≫ b := by
  change ((S.adjunction K).homEquiv X M').symm
    (f ≫ (Prod.sectR (op K) A ⋙ H).map b) =
      ((S.adjunction K).homEquiv X M).symm f ≫ b
  exact (S.adjunction K).homEquiv_naturality_right_symm f b

private lemma closed_eval_target
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (K M M' : A) (b : M ⟶ M') :
    S.tensor.map (H.map (𝟙 (op K), b), 𝟙 K) ≫ S.evaluation K M' =
      S.evaluation K M ≫ b := by
  let := S.monoidal
  simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorRight,
    Functor.flip, MonoidalCategory.curriedTensor, MonoidalCategory.tensorHom_id,
    Functor.comp_map, Prod.sectR, Functor.id_map] using
      (S.adjunction K).counit.naturality b

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open MonoidalCategory in
private lemma closed_naturality
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) :
    (∀ (K K' L M : A) (a : K' ⟶ K),
      S.composition K L M ≫
          H.map (a.op, 𝟙 M) =
        S.tensor.map
          (𝟙 (H.obj (op L, M)),
            H.map (a.op, 𝟙 L)) ≫
          S.composition K' L M) ∧
    (∀ (K L M M' : A) (b : M ⟶ M'),
      S.composition K L M ≫
          H.map (𝟙 (op K), b) =
        S.tensor.map
          (H.map (𝟙 (op L), b),
            𝟙 (H.obj (op K, L))) ≫
          S.composition K L M') ∧
    (∀ (K L L' M : A) (f : L ⟶ L'),
      S.tensor.map
          (𝟙 (H.obj (op L', M)),
            H.map (𝟙 (op K), f)) ≫
          S.composition K L' M =
        S.tensor.map
          (X := (H.obj (op L', M),
            H.obj (op K, L)))
          (Y := (H.obj (op L, M),
            H.obj (op K, L)))
          (H.map (f.op, 𝟙 M),
            𝟙 (H.obj (op K, L))) ≫
          S.composition K L M) := by
  let := S.monoidal
  let ev (K M : A) : H.obj (op K, M) ⊗ K ⟶ M := S.evaluation K M
  refine ⟨?_, ?_, ?_⟩
  · intro K K' L M a
    apply (S.transpose _ K' M).symm.injective
    rw [closed_uncurry_source, closed_uncurry_precomp]
    rw [closed_uncurry_composition, closed_uncurry_composition]
    simp only [CoefficientClosedStructure.tensor, tensor_obj, MonoidalCategory.tensor_map]
    change (𝟙 (H.obj (op L, M) ⊗ H.obj (op K, L)) ⊗ₘ a) ≫
      (α_ (H.obj (op L, M)) (H.obj (op K, L)) K).hom ≫
        (𝟙 _ ⊗ₘ ev K L) ≫ ev L M =
      ((𝟙 (H.obj (op L, M)) ⊗ₘ H.map (a.op, 𝟙 L)) ⊗ₘ 𝟙 K') ≫
        (α_ (H.obj (op L, M)) (H.obj (op K', L)) K').hom ≫
          (𝟙 _ ⊗ₘ ev K' L) ≫ ev L M
    have ha := associator_naturality (𝟙 (H.obj (op L, M)))
      (𝟙 (H.obj (op K, L))) a
    simp only [id_tensorHom_id] at ha
    have he : (H.map (a.op, 𝟙 L) ⊗ₘ 𝟙 K') ≫ ev K' L =
        (𝟙 (H.obj (op K, L)) ⊗ₘ a) ≫ ev K L := by
      simpa only [CoefficientClosedStructure.tensor, tensor_map] using
        closed_eval_source S K K' L a
    rw [reassoc_of% ha, associator_naturality_assoc]
    simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, he]
  · intro K L M M' b
    apply (S.transpose _ K M').symm.injective
    rw [closed_uncurry_postcomp, closed_uncurry_precomp]
    rw [closed_uncurry_composition, closed_uncurry_composition]
    simp only [CoefficientClosedStructure.tensor, tensor_obj, MonoidalCategory.tensor_map]
    change ((α_ (H.obj (op L, M)) (H.obj (op K, L)) K).hom ≫
      (𝟙 _ ⊗ₘ ev K L) ≫ ev L M) ≫ b =
      ((H.map (𝟙 (op L), b) ⊗ₘ 𝟙 (H.obj (op K, L))) ⊗ₘ 𝟙 K) ≫
        (α_ (H.obj (op L, M')) (H.obj (op K, L)) K).hom ≫
          (𝟙 _ ⊗ₘ ev K L) ≫ ev L M'
    have he : (H.map (𝟙 (op L), b) ⊗ₘ 𝟙 L) ≫ ev L M' =
        ev L M ≫ b := by
      simpa only [CoefficientClosedStructure.tensor, tensor_map] using
        closed_eval_target S L M M' b
    rw [associator_naturality_assoc]
    simp only [Category.assoc, id_tensorHom_id]
    rw [← he]
    simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  · intro K L L' M f
    apply (S.transpose _ K M).symm.injective
    rw [closed_uncurry_precomp, closed_uncurry_precomp]
    rw [closed_uncurry_composition, closed_uncurry_composition]
    simp only [CoefficientClosedStructure.tensor, tensor_obj, MonoidalCategory.tensor_map]
    change ((𝟙 (H.obj (op L', M)) ⊗ₘ H.map (𝟙 (op K), f)) ⊗ₘ 𝟙 K) ≫
      (α_ (H.obj (op L', M)) (H.obj (op K, L')) K).hom ≫
        (𝟙 _ ⊗ₘ ev K L') ≫ ev L' M =
      ((H.map (f.op, 𝟙 M) ⊗ₘ 𝟙 (H.obj (op K, L))) ⊗ₘ 𝟙 K) ≫
        (α_ (H.obj (op L, M)) (H.obj (op K, L)) K).hom ≫
          (𝟙 _ ⊗ₘ ev K L) ≫ ev L M
    have he₁ : (H.map (𝟙 (op K), f) ⊗ₘ 𝟙 K) ≫ ev K L' =
        ev K L ≫ f := by
      simpa only [CoefficientClosedStructure.tensor, tensor_map] using
        closed_eval_target S K L L' f
    have he₂ : (H.map (f.op, 𝟙 M) ⊗ₘ 𝟙 L) ≫ ev L M =
        (𝟙 (H.obj (op L', M)) ⊗ₘ f) ≫ ev L' M := by
      simpa only [CoefficientClosedStructure.tensor, tensor_map] using
        closed_eval_source S L' L M f
    rw [associator_naturality_assoc, associator_naturality_assoc]
    simp only [id_tensorHom_id, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id, he₁]
    rw [show (𝟙 (H.obj (op L', M)) ⊗ₘ ev K L ≫ f) =
      (𝟙 (H.obj (op L', M)) ⊗ₘ ev K L) ≫
        (𝟙 (H.obj (op L', M)) ⊗ₘ f) by
          rw [tensorHom_comp_tensorHom, Category.id_comp]]
    simp only [Category.assoc]
    rw [← he₂]
    simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

private lemma closed_pairing_coherence
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (U T P F G W V Z Y : A)
    (cUT : W ≅ S.tensor.obj (U, T)) (cTP : V ≅ S.tensor.obj (T, P))
    (cWP : Z ≅ S.tensor.obj (W, P)) (cUV : Y ≅ S.tensor.obj (U, V))
    (a : Z ⟶ Y)
    (ha : cWP.hom ≫ S.tensor.map
        (X := (W, P)) (Y := (S.tensor.obj (U, T), P)) (cUT.hom, 𝟙 P) ≫
        (S.monoidal.associator U T P).hom =
      a ≫ cUV.hom ≫ S.tensor.map (X := (U, V))
        (Y := (U, S.tensor.obj (T, P))) (𝟙 U, cTP.hom))
    (f : U ⟶ H.obj (op F, G)) (g : T ⟶ H.obj (op P, F)) (h : V ⟶ F)
    (hh : cTP.hom ≫ (S.transpose T P F).symm g = h) :
    cWP.hom ≫ (S.transpose W P G).symm
        (cUT.hom ≫ S.tensor.map (f, g) ≫ S.composition P F G) =
      a ≫ cUV.hom ≫ (S.transpose U V G).symm (f ≫ H.map (h.op, 𝟙 G)) := by
  let := S.monoidal
  have hn : S.tensor.map
      (X := (S.tensor.obj (U, T), P))
      (Y := (S.tensor.obj (H.obj (op F, G), H.obj (op P, F)), P))
      (S.tensor.map (X := (U, T))
        (Y := (H.obj (op F, G), H.obj (op P, F))) (f, g), 𝟙 P) ≫
      (S.monoidal.associator (H.obj (op F, G)) (H.obj (op P, F)) P).hom =
      (S.monoidal.associator U T P).hom ≫
        S.tensor.map (X := (U, S.tensor.obj (T, P)))
          (Y := (H.obj (op F, G), S.tensor.obj (H.obj (op P, F), P)))
          (f, S.tensor.map (X := (T, P)) (Y := (H.obj (op P, F), P)) (g, 𝟙 P)) := by
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map] using
      MonoidalCategory.associator_naturality f g (𝟙 P)
  erw [closed_uncurry_precomp, closed_uncurry_precomp, closed_uncurry_composition,
    closed_uncurry_source, closed_uncurry]
  erw [reassoc_of% hn]
  have hmap : S.tensor.map (X := (U, S.tensor.obj (T, P)))
      (Y := (H.obj (op F, G), S.tensor.obj (H.obj (op P, F), P)))
      (f, S.tensor.map (X := (T, P)) (Y := (H.obj (op P, F), P)) (g, 𝟙 P)) ≫
      S.tensor.map (X := (H.obj (op F, G), S.tensor.obj (H.obj (op P, F), P)))
        (Y := (H.obj (op F, G), F)) (𝟙 (H.obj (op F, G)), S.evaluation P F) =
      S.tensor.map (X := (U, S.tensor.obj (T, P)))
        (Y := (H.obj (op F, G), F)) (f, (S.transpose T P F).symm g) := by
    erw [← S.tensor.map_comp, closed_uncurry]
    simp only [prod_comp, Category.comp_id]
  erw [reassoc_of% hmap, reassoc_of% ha]
  have hmap' : S.tensor.map (X := (U, V))
      (Y := (U, S.tensor.obj (T, P))) (𝟙 U, cTP.hom) ≫
      S.tensor.map (X := (U, S.tensor.obj (T, P)))
        (Y := (H.obj (op F, G), F)) (f, (S.transpose T P F).symm g) =
      S.tensor.map (X := (U, V)) (Y := (H.obj (op F, G), F)) (f, h) := by
    erw [← S.tensor.map_comp]
    simp only [prod_comp, Category.id_comp, hh]
  erw [reassoc_of% hmap']
  have hmap'' : S.tensor.map (X := (U, V)) (Y := (U, F)) (𝟙 U, h) ≫
      S.tensor.map (X := (U, F)) (Y := (H.obj (op F, G), F)) (f, 𝟙 F) =
      S.tensor.map (X := (U, V)) (Y := (H.obj (op F, G), F)) (f, h) := by
    erw [← S.tensor.map_comp]
    simp only [prod_comp, Category.id_comp, Category.comp_id]
  erw [reassoc_of% hmap'']

private lemma map_three_comp
    {A B : Type*} [Category A] [Category B] (Q : A ⥤ B)
    {X₀ X₁ X₂ X₃ : A} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)
    (h : X₂ ⟶ X₃) (l : X₀ ⟶ X₃)
    (w : f ≫ g ≫ h = l) {Z : B} (a : Q.obj X₃ ⟶ Z) :
    Q.map f ≫ Q.map g ≫ Q.map h ≫ a = Q.map l ≫ a := by
  rw [← w]
  simp only [Functor.map_comp, Category.assoc]

private lemma closed_pairing_descent
    {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (U T A E P F G W V : B)
    (cUT : W ≅ S.tensor.obj (U, T)) (cAT : V ≅ S.tensor.obj (A, T))
    (q : W ⟶ V) (r : U ⟶ A) (a : A ⟶ H.obj (op F, G))
    (t : T ⟶ H.obj (op E, F)) (s : P ⟶ E) (g : T ⟶ H.obj (op P, F))
    (hq : q ≫ cAT.hom = cUT.hom ≫ S.tensor.map (r, 𝟙 T))
    (hg : t ≫ H.map (s.op, 𝟙 F) = g) :
    q ≫ cAT.hom ≫ S.tensor.map (a, t) ≫ S.composition E F G ≫ H.map (s.op, 𝟙 G) =
      cUT.hom ≫ S.tensor.map (r ≫ a, g) ≫ S.composition P F G := by
  rw [← Category.assoc q cAT.hom, hq]
  simp only [Category.assoc]
  rw [(closed_naturality S).1 E P F G s]
  simp only [← Category.assoc, ← S.tensor.map_comp, prod_comp,
    Category.id_comp, Category.comp_id, hg]

namespace HomCompositionProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open WeilConjectures.ZeroClassAux

attribute [local instance 4000] HomologicalComplex.monoidalCategory
attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric
attribute [local irreducible] tensorHomEquiv homComplexFunctor
  SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction Adjunction.rightAdjointLaxMonoidal
  RingedDerivedNative.chainEquiv

attribute [local irreducible] coefficientTotalTensor CoefficientTensorModels.iso
  derivedInternalHomOfUniverses ringedHomRepresentativeMap ringedHomComposition
  CoefficientClosedStructure.composition CoefficientClosedStructure.transpose
  CoefficientClosedStructure.evaluation

private lemma composition_on_kflats
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (N : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (D : RingedDerivedTensorCoherence.{c, v, u, w} J R S N β)
    (P T U F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hT : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) T)
    (hU : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) U)
    (f : U ⟶ homComplex (R := R) F G) (g : T ⟶ homComplex (R := R) P F) :
    (N.iso J R S U T hU hT).hom ≫
        S.tensor.map
          (DerivedCategory.Q.map f ≫ ringedHomRepresentativeMap.{c, v, u, w} J R F G,
            DerivedCategory.Q.map g ≫ ringedHomRepresentativeMap.{c, v, u, w} J R P F) ≫
        S.composition (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F)
          (DerivedCategory.Q.obj G) =
      DerivedCategory.Q.map ((coefficientTotalTensor.{u, c, v} J R).map (f, g) ≫
        ringedHomComposition.{c, v, u} J R P F G) ≫
          ringedHomRepresentativeMap.{c, v, u, w} J R P G := by
  let W := (coefficientTotalTensor.{u, c, v} J R).obj (U, T)
  let V := (coefficientTotalTensor.{u, c, v} J R).obj (T, P)
  have hW := coefficientTotalTensor_isKFlat.{u, c, v} J R U T hU hT
  have hV := coefficientTotalTensor_isKFlat.{u, c, v} J R T P hT hP
  let h := (RingedDerivedNative.chainEquiv.{c, v, u} J R T P F).symm g
  let κ : U ⟶ homComplex (R := R) V G :=
    f ≫ ((homComplexFunctor (R := R)).map h.op).app G
  let φ := (coefficientTotalTensor.{u, c, v} J R).map
    (X := (U, T)) (Y := (homComplex (R := R) F G, homComplex (R := R) P F)) (f, g) ≫
    ringedHomComposition.{c, v, u} J R P F G
  obtain ⟨a, hapure, ha⟩ := D.associator_model U T P hU hT hP
  have hchain : (RingedDerivedNative.chainEquiv.{c, v, u} J R W P G).symm φ =
      a.hom ≫ (RingedDerivedNative.chainEquiv.{c, v, u} J R U V G).symm κ := by
    apply triple_uncurry.{c, v, u} J R P T U F G f g a.hom
    intro p q r n hn V' x y z
    exact hapure p q r (p + q) (r + q) n rfl (by omega) hn (by omega) V' x y z
  have hnφ := normalized_uncurry.{c, v, u, w} J R S N W P G hW hP φ
  have hng := normalized_uncurry.{c, v, u, w} J R S N T P F hT hP g
  have hnκ := normalized_uncurry.{c, v, u, w} J R S N U V G hU hV κ
  have hκ : DerivedCategory.Q.map κ ≫
      ringedHomRepresentativeMap.{c, v, u, w} J R V G =
      (DerivedCategory.Q.map f ≫ ringedHomRepresentativeMap.{c, v, u, w} J R F G) ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          ((DerivedCategory.Q.map h).op, 𝟙 (DerivedCategory.Q.obj G)) := by
    dsimp only [κ]
    erw [Functor.map_comp, Category.assoc,
      ← representative_source.{c, v, u, w} J R F V G h, Category.assoc]
  erw [hκ] at hnκ
  have hWP : D.tensorIso W P (Or.inr hP) = N.iso J R S W P hW hP :=
    D.tensorIso_both W P hW hP
  have hUV : D.tensorIso U V (Or.inl hU) = N.iso J R S U V hU hV :=
    D.tensorIso_both U V hU hV
  change (D.tensorIso W P (Or.inr hP)).hom ≫
      S.tensor.map (X := (DerivedCategory.Q.obj W, DerivedCategory.Q.obj P))
        (Y := (S.tensor.obj (DerivedCategory.Q.obj U, DerivedCategory.Q.obj T),
          DerivedCategory.Q.obj P))
        ((N.iso J R S U T hU hT).hom, 𝟙 (DerivedCategory.Q.obj P)) ≫
        (S.monoidal.associator (DerivedCategory.Q.obj U) (DerivedCategory.Q.obj T)
          (DerivedCategory.Q.obj P)).hom =
    DerivedCategory.Q.map a.hom ≫ (D.tensorIso U V (Or.inl hU)).hom ≫
      S.tensor.map (X := (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V))
        (Y := (DerivedCategory.Q.obj U,
          S.tensor.obj (DerivedCategory.Q.obj T, DerivedCategory.Q.obj P)))
        (𝟙 (DerivedCategory.Q.obj U), (N.iso J R S T P hT hP).hom) at ha
  have ha' : (N.iso J R S W P hW hP).hom ≫
      S.tensor.map (X := (DerivedCategory.Q.obj W, DerivedCategory.Q.obj P))
        (Y := (S.tensor.obj (DerivedCategory.Q.obj U, DerivedCategory.Q.obj T),
          DerivedCategory.Q.obj P))
        ((N.iso J R S U T hU hT).hom, 𝟙 (DerivedCategory.Q.obj P)) ≫
        (S.monoidal.associator (DerivedCategory.Q.obj U) (DerivedCategory.Q.obj T)
          (DerivedCategory.Q.obj P)).hom =
    DerivedCategory.Q.map a.hom ≫ (N.iso J R S U V hU hV).hom ≫
      S.tensor.map (X := (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V))
        (Y := (DerivedCategory.Q.obj U,
          S.tensor.obj (DerivedCategory.Q.obj T, DerivedCategory.Q.obj P)))
        (𝟙 (DerivedCategory.Q.obj U), (N.iso J R S T P hT hP).hom) := by
    have hleft := congrArg (fun e :
        DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (W, P)) ≅
          S.tensor.obj (DerivedCategory.Q.obj W, DerivedCategory.Q.obj P) ↦
      e.hom ≫ S.tensor.map
        (X := (DerivedCategory.Q.obj W, DerivedCategory.Q.obj P))
        (Y := (S.tensor.obj (DerivedCategory.Q.obj U, DerivedCategory.Q.obj T),
          DerivedCategory.Q.obj P))
        ((N.iso J R S U T hU hT).hom, 𝟙 (DerivedCategory.Q.obj P)) ≫
        (S.monoidal.associator (DerivedCategory.Q.obj U) (DerivedCategory.Q.obj T)
          (DerivedCategory.Q.obj P)).hom) hWP
    have hright := congrArg (fun e :
        DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (U, V)) ≅
          S.tensor.obj (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V) ↦
      DerivedCategory.Q.map a.hom ≫ e.hom ≫ S.tensor.map
        (X := (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V))
        (Y := (DerivedCategory.Q.obj U,
          S.tensor.obj (DerivedCategory.Q.obj T, DerivedCategory.Q.obj P)))
        (𝟙 (DerivedCategory.Q.obj U), (N.iso J R S T P hT hP).hom)) hUV
    exact hleft.symm.trans (ha.trans hright)
  apply (S.transpose _ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj G)).symm.injective
  apply (cancel_epi (N.iso J R S W P hW hP).hom).1
  calc
    _ = DerivedCategory.Q.map a.hom ≫ (N.iso J R S U V hU hV).hom ≫
        (S.transpose (DerivedCategory.Q.obj U) (DerivedCategory.Q.obj V)
          (DerivedCategory.Q.obj G)).symm
          ((DerivedCategory.Q.map f ≫ ringedHomRepresentativeMap.{c, v, u, w} J R F G) ≫
            (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
              ((DerivedCategory.Q.map h).op, 𝟙 (DerivedCategory.Q.obj G))) := by
      exact closed_pairing_coherence S
        (DerivedCategory.Q.obj U) (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj G)
        (DerivedCategory.Q.obj W) (DerivedCategory.Q.obj V)
        (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (W, P)))
        (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (U, V)))
        (N.iso J R S U T hU hT) (N.iso J R S T P hT hP)
        (N.iso J R S W P hW hP) (N.iso J R S U V hU hV)
        (DerivedCategory.Q.map a.hom) ha'
        (DerivedCategory.Q.map f ≫ ringedHomRepresentativeMap.{c, v, u, w} J R F G)
        (DerivedCategory.Q.map g ≫ ringedHomRepresentativeMap.{c, v, u, w} J R P F)
        (DerivedCategory.Q.map h) hng
    _ = DerivedCategory.Q.map a.hom ≫
        DerivedCategory.Q.map ((RingedDerivedNative.chainEquiv.{c, v, u} J R U V G).symm κ) :=
      congrArg (fun k ↦ DerivedCategory.Q.map a.hom ≫ k) hnκ
    _ = DerivedCategory.Q.map ((RingedDerivedNative.chainEquiv.{c, v, u} J R W P G).symm φ) :=
      (DerivedCategory.Q.map_comp a.hom
        ((RingedDerivedNative.chainEquiv.{c, v, u} J R U V G).symm κ)).symm.trans
          (congrArg (fun k ↦ DerivedCategory.Q.map k) hchain.symm)
    _ = _ := hnφ.symm

private lemma model
  [HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R)]
  [∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
    GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (N : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (D : RingedDerivedTensorCoherence.{c, v, u, w} J R S N β)
    (E F G T : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (t : T ⟶ homComplex (R := R) E F)
    (ht : CochainComplex.IsKFlatResolutionIndependentCoefficients (J := J) (R := R) t) :
    (D.tensorIso (homComplex (R := R) F G) T (Or.inr ht.2)).hom ≫
        S.tensor.map
          (ringedHomRepresentativeMap.{c, v, u, w} J R F G,
            DerivedCategory.Q.map t ≫ ringedHomRepresentativeMap.{c, v, u, w} J R E F) ≫
        S.composition (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F)
          (DerivedCategory.Q.obj G) =
      DerivedCategory.Q.map
        ((coefficientTotalTensor.{u, c, v} J R).map
          (𝟙 (homComplex (R := R) F G), t) ≫ ringedHomComposition.{c, v, u} J R E F G) ≫
        ringedHomRepresentativeMap.{c, v, u, w} J R E G := by
  let A := homComplex (R := R) F G
  obtain ⟨U, r, hU, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max c v u, c, v}
      (C := C) (J := J) (R := R) A
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max c v u, c, v}
      (C := C) (J := J) (R := R) E
  let preF : homComplex (R := R) E F ⟶ homComplex (R := R) P F :=
    ((homComplexFunctor (R := R)).map s.op).app F
  let preG : homComplex (R := R) E G ⟶ homComplex (R := R) P G :=
    ((homComplexFunctor (R := R)).map s.op).app G
  let g : T ⟶ homComplex (R := R) P F := t ≫ preF
  let φ := (coefficientTotalTensor.{u, c, v} J R).map
    (X := (U, T)) (Y := (A, homComplex (R := R) P F)) (r, g) ≫
    ringedHomComposition.{c, v, u} J R P F G
  let q := DerivedCategory.Q.{w}.map
    ((coefficientTotalTensor.{u, c, v} J R).map (X := (U, T)) (Y := (A, T)) (r, 𝟙 T))
  let z := (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
    (X := (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj G))
    (Y := (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj G))
    ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj G))
  have : IsIso (DerivedCategory.Q.{w}.map r) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hr
  have : IsIso (DerivedCategory.Q.{w}.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hs
  have hq := D.tensorIso_naturality U T A T (Or.inl hU) (Or.inr ht.2) r (𝟙 T)
  have hUT : (D.tensorIso U T (Or.inl hU)).hom =
      (N.iso J R S U T hU ht.2).hom :=
    congrArg Iso.hom (D.tensorIso_both U T hU ht.2)
  have hqboth : q ≫ (D.tensorIso A T (Or.inr ht.2)).hom =
      (N.iso J R S U T hU ht.2).hom ≫
        S.tensor.map (X := (DerivedCategory.Q.obj U, DerivedCategory.Q.obj T))
          (Y := (DerivedCategory.Q.obj A, DerivedCategory.Q.obj T))
          (DerivedCategory.Q.map r, 𝟙 (DerivedCategory.Q.obj T)) := by
    have hh := congrArg (fun k :
        DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (U, T)) ⟶
          S.tensor.obj (DerivedCategory.Q.obj U, DerivedCategory.Q.obj T) ↦
      k ≫ S.tensor.map (X := (DerivedCategory.Q.obj U, DerivedCategory.Q.obj T))
        (Y := (DerivedCategory.Q.obj A, DerivedCategory.Q.obj T))
        (DerivedCategory.Q.map r, DerivedCategory.Q.map (𝟙 T))) hUT
    have hi := congrArg (fun k : DerivedCategory.Q.obj T ⟶ DerivedCategory.Q.obj T ↦
      (N.iso J R S U T hU ht.2).hom ≫
        S.tensor.map (X := (DerivedCategory.Q.obj U, DerivedCategory.Q.obj T))
          (Y := (DerivedCategory.Q.obj A, DerivedCategory.Q.obj T))
          (DerivedCategory.Q.map r, k)) (DerivedCategory.Q.map_id T)
    exact hq.trans (hh.trans hi)
  have : IsIso (Prod.mkHom (DerivedCategory.Q.{w}.map r)
      (DerivedCategory.Q.{w}.map (𝟙 T))) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso q := by
    have he : q = (D.tensorIso U T (Or.inl hU)).hom ≫
        S.tensor.map (DerivedCategory.Q.map r, DerivedCategory.Q.map (𝟙 T)) ≫
          (D.tensorIso A T (Or.inr ht.2)).inv := by
      apply (cancel_mono (D.tensorIso A T (Or.inr ht.2)).hom).1
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hq
    erw [he]
    infer_instance
  have : IsIso (Prod.mkHom (DerivedCategory.Q.{w}.map s).op
      (𝟙 (DerivedCategory.Q.{w}.obj G))) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso z := by dsimp only [z]; infer_instance
  apply (cancel_epi q).1
  apply (cancel_mono z).1
  have hk := composition_on_kflats.{c, v, u, w} J R S N β D P T U F G hP ht.2 hU r g
  have hc : (coefficientTotalTensor.{u, c, v} J R).map
      (X := (U, T)) (Y := (A, T)) (r, 𝟙 T) ≫
      (coefficientTotalTensor.{u, c, v} J R).map
        (X := (A, T)) (Y := (A, homComplex (R := R) E F)) (𝟙 A, t) ≫
        ringedHomComposition.{c, v, u} J R E F G ≫ preG = φ := by
    erw [composition_source.{c, v, u} J R E P F G s]
    simp only [← Category.assoc, ← (coefficientTotalTensor.{u, c, v} J R).map_comp]
    rfl
  have hg : (DerivedCategory.Q.map t ≫
      ringedHomRepresentativeMap.{c, v, u, w} J R E F) ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          ((DerivedCategory.Q.map s).op, 𝟙 (DerivedCategory.Q.obj F)) =
      DerivedCategory.Q.map g ≫ ringedHomRepresentativeMap.{c, v, u, w} J R P F := by
    have he := congrArg (fun k ↦ DerivedCategory.Q.map t ≫ k)
      (representative_source.{c, v, u, w} J R E P F s)
    calc
      _ = DerivedCategory.Q.map t ≫ DerivedCategory.Q.map preF ≫
          ringedHomRepresentativeMap.{c, v, u, w} J R P F := by
        convert he using 0
        simp only [preF, Category.assoc]
        rfl
      _ = _ := (DerivedCategory.Q.map_comp_assoc t preF
        (ringedHomRepresentativeMap.{c, v, u, w} J R P F)).symm
  calc
    _ = (N.iso J R S U T hU ht.2).hom ≫
        S.tensor.map
          (DerivedCategory.Q.map r ≫ ringedHomRepresentativeMap.{c, v, u, w} J R F G,
            DerivedCategory.Q.map g ≫ ringedHomRepresentativeMap.{c, v, u, w} J R P F) ≫
          S.composition (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F)
            (DerivedCategory.Q.obj G) := by
      simpa only [Category.assoc] using closed_pairing_descent S
        (DerivedCategory.Q.obj U) (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F)
        (DerivedCategory.Q.obj G)
        (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (U, T)))
        (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (A, T)))
        (N.iso J R S U T hU ht.2) (D.tensorIso A T (Or.inr ht.2)) q
        (DerivedCategory.Q.map r) (ringedHomRepresentativeMap.{c, v, u, w} J R F G)
        (DerivedCategory.Q.map t ≫ ringedHomRepresentativeMap.{c, v, u, w} J R E F)
        (DerivedCategory.Q.map s)
        (DerivedCategory.Q.map g ≫ ringedHomRepresentativeMap.{c, v, u, w} J R P F)
        hqboth hg
    _ = DerivedCategory.Q.map φ ≫
        ringedHomRepresentativeMap.{c, v, u, w} J R P G := hk
    _ = _ := by
      symm
      dsimp only [q, z]
      simp only [Category.assoc]
      erw [representative_source.{c, v, u, w} J R E P G s]
      have he := map_three_comp DerivedCategory.Q
        ((coefficientTotalTensor.{u, c, v} J R).map
          (X := (U, T)) (Y := (A, T)) (r, 𝟙 T))
        ((coefficientTotalTensor.{u, c, v} J R).map
          (X := (A, T)) (Y := (A, homComplex (R := R) E F)) (𝟙 A, t) ≫
            ringedHomComposition.{c, v, u} J R E F G)
        preG φ (by simpa only [Category.assoc] using hc)
        (ringedHomRepresentativeMap.{c, v, u, w} J R P G)
      convert he using 0
      simp only [preG]
      rfl

end HomCompositionProof

end CategoryTheory
