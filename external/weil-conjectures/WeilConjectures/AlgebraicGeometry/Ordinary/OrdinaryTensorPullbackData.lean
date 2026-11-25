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
public import WeilConjectures.Algebra.Homology.SixFunctors.TensorSection

/-! # Ordinary tensor comparison data with independent coefficient size

## References

* Stacks 03EK
* Stacks 03EL and 0G7E
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace WeilConjectures.SemilinearSections

/-- The usual sheafified pure tensor, at an independent coefficient size. -/
abbrev tensorSectionAtSize {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    (M N : Mod.{c, v, r} J R) (V : Cᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V) :
    ((SheafOfModules.monoidalCategory R).tensorObj M N).val.obj V :=
  SheafOfModules.sheafTensorSection R M N V x y

section Comparison
variable {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K]
  (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
  (phi : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{r} J K).obj S)
  (F : Mod.{c, v, r} J R ⥤ Mod.{c, v, r} K S) [F.Additive]
  (adj : F ⊣ SheafOfModules.pushforward.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map phi))

local instance (M : Mod.{c, v, r} K S) {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    Module (S.obj.obj Y)
      ((ModuleCat.restrictScalars ((ring K S).obj.map f).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (S.obj.obj Y) (M.val.obj Y))

/-- The scalar-generator formula and two-variable naturality. -/
def OrdinaryTensorNormalized
    (e : ∀ M N : Mod.{c, v, r} J R,
      F.obj ((SheafOfModules.monoidalCategory R).tensorObj M N) ≅
        (SheafOfModules.monoidalCategory S).tensorObj (F.obj M) (F.obj N)) : Prop :=
  (∀ (M N : Mod.{c, v, r} J R) (V : C) (W : D) (p : W ⟶ U.obj V)
      (x : M.val.obj (op V)) (y : N.val.obj (op V)) (a : S.obj.obj (op W)),
    (e M N).hom.val.app (op W)
        (a • (F.obj ((SheafOfModules.monoidalCategory R).tensorObj M N)).val.map p.op
          ((adj.unit.app ((SheafOfModules.monoidalCategory R).tensorObj M N)).val.app
            (op V) (tensorSectionAtSize J R M N (op V) x y))) =
      tensorSectionAtSize K S (F.obj M) (F.obj N) (op W)
        (a • (F.obj M).val.map p.op ((adj.unit.app M).val.app (op V) x))
        ((F.obj N).val.map p.op ((adj.unit.app N).val.app (op V) y))) ∧
  ∀ (M M' N N' : Mod.{c, v, r} J R) (a : M ⟶ M') (b : N ⟶ N'),
    F.map ((SheafOfModules.monoidalCategory R).tensorHom a b) ≫ (e M' N').hom =
      (e M N).hom ≫ (SheafOfModules.monoidalCategory S).tensorHom (F.map a) (F.map b)

/-- The ordinary tensor comparison and preservation of flat-term representatives.
All remaining fields are propositions; normalization determines the ordinary isomorphisms. -/
structure OrdinaryTensorPullbackData where
  /-- The comparison on ordinary sheaf modules. -/
  ordinary : ∀ M N : Mod.{c, v, r} J R,
    F.obj ((SheafOfModules.monoidalCategory R).tensorObj M N) ≅
      (SheafOfModules.monoidalCategory S).tensorObj (F.obj M) (F.obj N)
  /-- Generator normalization and naturality. -/
  normalized : OrdinaryTensorNormalized J K U R S phi F adj ordinary
  /-- Preservation of the simultaneous flat-term K-flat representative class. -/
  flat : ∀ P : CochainComplex (Mod.{c, v, r} J R) ℤ,
    P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
    CochainComplex.IsKFlatIndependentCoefficients
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := S)
        (((F.mapHomologicalComplex (.up ℤ)).obj P).X n)
end Comparison
end WeilConjectures.SemilinearSections
