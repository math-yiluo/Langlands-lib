/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
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
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-! # Tensor compatibility of derived coefficient extension

## References

* Stacks 03EK, 06YY, 07A4 and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]

open CategoryTheory.MonoidalCategory CategoryTheory.Functor SheafOfModules
open SheafOfModules.ScalarHomOrdinary

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory
  WeilConjectures.CoefficientTensorModels.iso

namespace ScalarTensorOrdinary

variable {J} {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
  (A : ScalarData.{c, v, max c v r} φ)

private def extensionComparison (M : Mod.{c, v, max c v r} J R) :
    A.model.E.obj M ≅
      changeOfRingsOfUniverses.{v, c, max c v r, max c v r} φ M :=
  eqToIso (A.model.obj_eq M) ≪≫ extensionIso.{c, v, max c v r} φ M

private theorem extensionComparison_unit (M : Mod.{c, v, max c v r} J R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (extensionComparison.{c, v, r} φ A M).hom.val.app U
      ((A.ordinaryAdjunction.unit.app M).val.app U x) =
      SheafOfModules.scalarExtensionSection.{c, v, max c v r, max c v r} φ M U 1 x := by
  change (extensionIso.{c, v, max c v r} φ M).hom.val.app U
    ((eqToHom (A.model.obj_eq M)).val.app U
      ((A.ordinaryAdjunction.unit.app M).val.app U x)) = _
  rw [A.unit_section]
  exact extensionIso_unit.{c, v, max c v r} φ M U x

private def ordinaryComparison (k : ScalarExtensionTensorCore.{c, v, max c v r} R S φ)
    (M N : Mod.{c, v, max c v r} J R) :
    A.model.E.obj (ordinaryTensor.{c, v, r} J R M N) ≅
      ordinaryTensor.{c, v, r} J S (A.model.E.obj M) (A.model.E.obj N) :=
  extensionComparison.{c, v, r} φ A _ ≪≫
    (extensionFunctor.{c, v, max c v r} φ).mapIso
      (tensorIsoSite.{c, v, max c v r} R M N) ≪≫
    k.tensorComparison M N ≪≫
      (tensorIsoSite.{c, v, max c v r} S (changeOfRingsOfUniverses.{v, c, max c v r, max c v r} φ M)
        (changeOfRingsOfUniverses.{v, c, max c v r, max c v r} φ N)).symm ≪≫
      @tensorIso _ _ (monoidalCategory S) _ _ _ _
        (extensionComparison.{c, v, r} φ A M).symm (extensionComparison.{c, v, r} φ A N).symm

private theorem extensionComparison_inv_unit (M : Mod.{c, v, max c v r} J R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (extensionComparison.{c, v, r} φ A M).inv.val.app U
      (SheafOfModules.scalarExtensionSection.{c, v, max c v r, max c v r} φ M U 1 x) =
      (A.ordinaryAdjunction.unit.app M).val.app U x := by
  rw [← extensionComparison_unit.{c, v, r} φ A M U x]
  exact congrArg (fun f ↦ f.val.app U ((A.ordinaryAdjunction.unit.app M).val.app U x))
    (extensionComparison.{c, v, r} φ A M).hom_inv_id

private theorem ordinaryComparison_unit (k : ScalarExtensionTensorCore.{c, v, max c v r} R S φ)
    (M N : Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (ordinaryComparison.{c, v, r} φ A k M N).hom.val.app U
      ((A.ordinaryAdjunction.unit.app _).val.app U (pure R M N U x y)) =
    pure S _ _ U ((A.ordinaryAdjunction.unit.app M).val.app U x)
      ((A.ordinaryAdjunction.unit.app N).val.app U y) := by
  let a := (extensionComparison.{c, v, r} φ A M).inv
  let b := (extensionComparison.{c, v, r} φ A N).inv
  let f := (changeOfRingsHomOfUniverses.{v, c, max c v r, max c v r} φ _
    (tensorIsoSite.{c, v, max c v r} R M N).hom).val.app U
  let g := (k.tensorComparison M N).hom.val.app U
  let h := (tensorIsoSite.{c, v, max c v r} S
    (changeOfRingsOfUniverses.{v, c, max c v r, max c v r} φ M)
    (changeOfRingsOfUniverses.{v, c, max c v r, max c v r} φ N)).inv.val.app U
  have h₁ := (congrArg f
    (extensionComparison_unit.{c, v, r} φ A _ U (pure R M N U x y))).trans
      (scalarExtension_map_tmul.{c, v, max c v r, max c v r} φ
        (tensorIsoSite.{c, v, max c v r} R M N).hom U 1 (pure R M N U x y))
  have h₂ := h₁.trans (congrArg
    (SheafOfModules.scalarExtensionSection.{c, v, max c v r, max c v r} φ _ U 1)
      (tensorIsoSite_pure.{c, v, max c v r} R M N U x y))
  have h₃ := (congrArg g h₂).trans (k.tensor_tmul M N U 1 x y)
  have h₄ := (congrArg h h₃).trans
    (tensorIsoSite_inv_pure.{c, v, max c v r} S _ _ U _ _)
  have h₅ := (congrArg (((monoidalCategory S).tensorHom a b).val.app U) h₄).trans
    (pure_map.{c, v, max c v r} S a b U _ _)
  exact h₅.trans (congrArg₂ (pure S (A.model.E.obj M) (A.model.E.obj N) U)
    (extensionComparison_inv_unit.{c, v, r} φ A M U x)
    (extensionComparison_inv_unit.{c, v, r} φ A N U y))

attribute [local irreducible] ordinaryComparison

private theorem ordinary_exists :
    ∃ e : ∀ M N : Mod.{c, v, max c v r} J R,
      A.model.E.obj (ordinaryTensor.{c, v, r} J R M N) ≅
        ordinaryTensor.{c, v, r} J S (A.model.E.obj M) (A.model.E.obj N),
      (∀ {M M' N N' : Mod.{c, v, max c v r} J R} (f : M ⟶ M') (g : N ⟶ N'),
        A.model.E.map (ordinaryTensorHom.{c, v, r} J R f g) ≫ (e M' N').hom =
          (e M N).hom ≫ ordinaryTensorHom.{c, v, r} J S
            (A.model.E.map f) (A.model.E.map g)) ∧
      ∀ M N U x y, (e M N).hom.val.app U
        ((A.ordinaryAdjunction.unit.app _).val.app U (pure R M N U x y)) =
      pure S _ _ U ((A.ordinaryAdjunction.unit.app M).val.app U x)
        ((A.ordinaryAdjunction.unit.app N).val.app U y) := by
  classical
  obtain ⟨k⟩ := exists_scalarExtensionTensorCore.{c, v, max c v r} R S φ
  let e := ordinaryComparison.{c, v, r} φ A k
  have he := ordinaryComparison_unit.{c, v, r} φ A k
  refine ⟨e, ?_, he⟩
  intro M M' N N' f g
  apply (A.ordinaryAdjunction.homEquiv _ _).injective
  apply pure_hom_ext.{c, v, max c v r} R M N ((res.{c, v, max c v r} φ).obj _)
  intro U x y
  have hu (P Q : Mod.{c, v, max c v r} J R) (h : P ⟶ Q) (z : P.val.obj U) :
      (A.model.E.map h).val.app U ((A.ordinaryAdjunction.unit.app P).val.app U z) =
        (A.ordinaryAdjunction.unit.app Q).val.app U (h.val.app U z) :=
    (congrArg (fun k ↦ k.val.app U z) (A.ordinaryAdjunction.unit.naturality h)).symm
  change (e M' N').hom.val.app U
      ((A.model.E.map ((monoidalCategory R).tensorHom f g)).val.app U _) =
    ((monoidalCategory S).tensorHom (A.model.E.map f) (A.model.E.map g)).val.app U
      ((e M N).hom.val.app U _)
  calc
    _ = (e M' N').hom.val.app U
        ((A.ordinaryAdjunction.unit.app _).val.app U
          (((monoidalCategory R).tensorHom f g).val.app U (pure R M N U x y))) :=
      congrArg ((e M' N').hom.val.app U) (hu _ _ _ (pure R M N U x y))
    _ = (e M' N').hom.val.app U
        ((A.ordinaryAdjunction.unit.app _).val.app U
          (pure R M' N' U (f.val.app U x) (g.val.app U y))) :=
      congrArg (fun z : ((monoidalCategory R).tensorObj M' N').val.obj U ↦
        (e M' N').hom.val.app U ((A.ordinaryAdjunction.unit.app _).val.app U z))
          (pure_map.{c, v, max c v r} R f g U x y)
    _ = pure S _ _ U
        ((A.ordinaryAdjunction.unit.app M').val.app U (f.val.app U x))
        ((A.ordinaryAdjunction.unit.app N').val.app U (g.val.app U y)) :=
      he M' N' U (f.val.app U x) (g.val.app U y)
    _ = pure S _ _ U
        ((A.model.E.map f).val.app U ((A.ordinaryAdjunction.unit.app M).val.app U x))
        ((A.model.E.map g).val.app U ((A.ordinaryAdjunction.unit.app N).val.app U y)) :=
      congrArg₂ (pure S (A.model.E.obj M') (A.model.E.obj N') U)
        (hu M M' f x).symm (hu N N' g y).symm
    _ = ((monoidalCategory S).tensorHom (A.model.E.map f) (A.model.E.map g)).val.app U
        (pure S _ _ U ((A.ordinaryAdjunction.unit.app M).val.app U x)
          ((A.ordinaryAdjunction.unit.app N).val.app U y)) :=
      (pure_map.{c, v, max c v r} S (A.model.E.map f) (A.model.E.map g) U
        ((A.ordinaryAdjunction.unit.app M).val.app U x)
        ((A.ordinaryAdjunction.unit.app N).val.app U y)).symm
    _ = _ := congrArg
      (((monoidalCategory S).tensorHom (A.model.E.map f) (A.model.E.map g)).val.app U)
        (he M N U x y).symm

private theorem unit_eq (M : Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) :
    scalarExtensionSection.{c, v, r} φ A M U x =
      (A.ordinaryAdjunction.unit.app M).val.app U x := by
  unfold scalarExtensionSection
  rw [← A.unit_section]
  exact congrArg (fun f ↦ f.val.app U ((A.ordinaryAdjunction.unit.app M).val.app U x))
    (eqToIso (A.model.obj_eq M)).hom_inv_id

end ScalarTensorOrdinary

private theorem reverseTensorSquare {K : Type*} [Category* K]
    {X₀ X₁ X₂ X₃ X₄ X₅ : K}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₀ ≅ X₄) (e : X₄ ≅ X₅) (f : X₅ ≅ X₃)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom) :
    f.hom ≫ c.inv ≫ b.inv ≫ a.inv ≫ d.hom = e.inv := by
  have hd : d.hom = a.hom ≫ b.hom ≫ c.hom ≫ f.inv ≫ e.inv := by
    rw [reassoc_of% h]
    simp
  rw [hd]
  simp

/-- Scalar extension commutes with the tensor of the actual K-flat models. -/
theorem semilinearScalarTensor
    (R S : Sheaf J CommRingCat.{max c v r}) (φ : R ⟶ S)
    (scalar : ScalarData.{c, v, max c v r} φ)
    (source : Closed.{c, v, r} J R) (target : Closed.{c, v, r} J S)
    (sourceModels : Models.{c, v, r} J R source)
    (targetModels : Models.{c, v, r} J S target) :
    ∃ γ : source.tensor ⋙ scalar.T ≅ (scalar.T.prod scalar.T) ⋙ target.tensor,
      Nonempty (ScalarTensorComparisonModel.{c, v, r} J R S φ scalar source target
        sourceModels targetModels γ) := by
  classical
  let A := Mod.{c, v, max c v r} J R
  let B := Mod.{c, v, max c v r} J S
  let E := scalar.model.E
  let := monoidalCategory R
  let := monoidalCategory S
  let := symmetricCategory R
  let := symmetricCategory S
  have (X : A) : (tensorLeft X).Additive := tensorLeft_additive_independent R X
  have (X : A) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  have (X : B) : (tensorLeft X).Additive := tensorLeft_additive_independent S X
  have (X : B) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  let : MonoidalPreadditive A :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let : MonoidalPreadditive B :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  obtain ⟨e, he, hgen⟩ := ScalarTensorOrdinary.ordinary_exists.{c, v, r} φ scalar
  let F := E.mapHomologicalComplex (.up ℤ)
  let tR := totalTensor.{c, v, r} J R
  let tS := totalTensor.{c, v, r} J S
  have hiso (P Q : CochainComplex A ℤ) :
      IsIso (tensorPullbackTotal E e he P Q) :=
    tensorPullbackTotal_isIso E e he (res φ) scalar.ordinaryAdjunction P Q
  let b0 : (F.prod F) ⋙ tS ≅ tR ⋙ F := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (tensorPullbackTotal E e he X.1 X.2)
      (hiso X.1 X.2)) (by
        intro X Y f
        dsimp only [F, tR, tS, Functor.comp_map, Functor.prod_map]
        simp only [totalTensor, coefficientTotalTensor, Functor.uncurry_obj_map,
          Functor.map₂HomologicalComplex, asIso_hom,
          CategoryTheory.ScalarHomTensor.tensorMap_factor]
        exact CategoryTheory.ScalarHomTensor.tensorPullbackTotal_naturality E e he f.1 f.2)
  have hs (P Q : CochainComplex A ℤ) (p q k : ℤ) (h : p + q = k) :
      tensorSummand.{c, v, r} J S (F.obj P) (F.obj Q) p q k h ≫
          ((b0.app (P, Q)).hom).f k =
        (e (P.X p) (Q.X q)).inv ≫
          E.map (tensorSummand.{c, v, r} J R P Q p q k h) := by
    change _ ≫ tensorPullbackTotalComponent E e P Q k = _
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
  let PS : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
  have hF : ∀ P, PR P → PS (F.obj P) := fun P hp ↦
    changeOfRings_isKFlat_independentCoefficients.{c, v, max c v r} φ P E scalar.model.obj_eq
      scalar.model.map_eq hp
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  obtain ⟨gamma, hgamma, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q F scalar.T scalar.model.ε PR PS hF ff' tR tS
    source.tensor target.tensor sourceModels.comparison targetModels.comparison b0.symm
    scalar.model.computes
    (fun P Q hp hq ↦ scalar.model.computes _
      (coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hp hq))
  refine ⟨gamma, ⟨{
    ordinary := e
    chain := fun P Q ↦ (b0.app (P, Q)).hom
    summand := hs
    kflat := fun P hp _ ↦ hF P hp
    derived := ?_
    ordinary_pure := ?_ }⟩⟩
  · intro P Q hp hq flatP flatQ hpq
    have hh : scalar.T.map (tensorModelIso.{c, v, r} J R source sourceModels P Q hp hq).hom ≫
      gamma.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      target.tensor.map (Prod.mkHom (scalarEpsilonIso.{c, v, r} φ scalar P hp).hom
        (scalarEpsilonIso.{c, v, r} φ scalar Q hq).hom) =
      (scalarEpsilonIso.{c, v, r} φ scalar (tR.obj (P, Q)) hpq).hom ≫
        DerivedCategory.Q.map (b0.app (P, Q)).inv ≫
        (tensorModelIso.{c, v, r} J S target targetModels (F.obj P) (F.obj Q)
          (hF P hp) (hF Q hq)).hom := by
      simpa only [tensorModelIso, CoefficientTensorModels.iso, Iso.app_hom,
        scalarEpsilonIso, asIso_hom, Iso.symm_hom, Iso.app_inv,
        tR, totalTensor, F, PR, Functor.comp_obj, Functor.prod_obj] using hgamma P Q hp hq
    exact reverseTensorSquare
      (scalar.T.mapIso (tensorModelIso.{c, v, r} J R source sourceModels P Q hp hq))
      (gamma.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
      (target.tensor.mapIso ((scalarEpsilonIso.{c, v, r} φ scalar P hp).prod
        (scalarEpsilonIso.{c, v, r} φ scalar Q hq)))
      (scalarEpsilonIso.{c, v, r} φ scalar (tR.obj (P, Q)) hpq)
      (DerivedCategory.Q.mapIso (b0.app (P, Q)).symm)
      (tensorModelIso.{c, v, r} J S target targetModels (F.obj P) (F.obj Q)
        (hF P hp) (hF Q hq)) hh
  · intro M N U x y
    simpa only [ScalarTensorOrdinary.unit_eq.{c, v, r}, tensorSection,
      SheafOfModules.ScalarHomOrdinary.pure] using hgen M N U x y

end WeilConjectures.SemilinearSections
