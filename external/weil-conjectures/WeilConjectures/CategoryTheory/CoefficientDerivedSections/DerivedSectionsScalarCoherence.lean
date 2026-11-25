/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.PUnit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Category.Grp.Biproducts
/-! # Coherent scalar comparison for unbounded derived global sections

Source: Stacks Project, sites-cohomology.tex, Tag 0D6E, lemma-derived-pushforward-composition
(blueprint: lem-coef-derived-sections-scalar-coherence).

The displayed localization factors make the source's identifications explicit. They
normalize derived scalar restriction, its composition comparison, and its identity.
The derived-unit equation uniquely fixes sigma, and the K-injective representative
formula identifies it with the canonical ringed-topos composition comparison.

## Main statements

* `derivedSectionsScalarCoherence`: existence, uniqueness, invertibility, the canonical
  resolution formula, the coefficient cocycle, and the identity law.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CoefficientDerivedSections

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The existing module-sheaf category for a commutative coefficient sheaf.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence).
-/
abbrev coefficientModules (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u, u, u, u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- The existing scalar restriction along a morphism of coefficient sheaves.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence).
-/
def coefficientRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    coefficientModules S ⥤ coefficientModules R :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map a)

/-- Scalar restriction is the existing additive functor.
Source: Stacks Project, modules.tex, restriction of scalars
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
instance coefficientRestriction_additive {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    (coefficientRestriction a).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map a)).Additive

/-- Global sections of the underlying abelian sheaf, with its abelian group structure.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence).
Mathlib's global-sections adjunction identifies this with maps from the terminal
set sheaf to the underlying set sheaf. No terminal object of the site is needed.
-/
def coefficientSections (R : Sheaf J CommRingCat.{u}) :
    coefficientModules R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf _ ⋙ Sheaf.Γ J AddCommGrpCat.{u}

/-- Global sections is the existing additive functor.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
instance coefficientSections_additive (R : Sheaf J CommRingCat.{u}) :
    (coefficientSections R).Additive := by
  change (SheafOfModules.toSheaf _ ⋙ Sheaf.Γ J AddCommGrpCat.{u}).Additive
  infer_instance

/-- Termwise scalar restriction on unbounded cochain complexes.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence).
-/
def coefficientComplexRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :=
  (coefficientRestriction a).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise global sections on unbounded complexes.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def coefficientComplexSections (R : Sheaf J CommRingCat.{u}) :=
  (coefficientSections R).mapHomologicalComplex (.up ℤ)

/-- The canonical composition isomorphism for scalar restriction.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def coefficientRestrictionComp {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) :
    coefficientRestriction b ⋙ coefficientRestriction a ≅ coefficientRestriction (a ≫ b) :=
  Iso.refl _

/-- Composition of termwise scalar restriction.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def coefficientComplexRestrictionComp {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) :
    coefficientComplexRestriction b ⋙ coefficientComplexRestriction a ≅
      coefficientComplexRestriction (a ≫ b) :=
  Functor.mapHomologicalComplexCompIso (coefficientRestrictionComp a b) (.up ℤ)

/-- The canonical identity isomorphism for scalar restriction.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def coefficientRestrictionId (R : Sheaf J CommRingCat.{u}) :
    coefficientRestriction (𝟙 R) ≅ 𝟭 (coefficientModules R) := Iso.refl _

/-- Identity of termwise scalar restriction.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def coefficientComplexRestrictionId (R : Sheaf J CommRingCat.{u}) :
    coefficientComplexRestriction (𝟙 R) ≅ 𝟭 (CochainComplex (coefficientModules R) ℤ) :=
  NatIso.mapHomologicalComplex (coefficientRestrictionId R) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (coefficientModules R) (.up ℤ)

/-- Restriction preserves the underlying abelian sheaf.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def coefficientRestrictionForget {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    coefficientRestriction a ⋙ SheafOfModules.toSheaf.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ≅
      SheafOfModules.toSheaf.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) := Iso.refl _

/-- Scalar restriction preserves the underlying global sections.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def coefficientSectionsRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    coefficientRestriction a ⋙ coefficientSections R ≅ coefficientSections S :=
  Functor.isoWhiskerRight (coefficientRestrictionForget a) (Sheaf.Γ J AddCommGrpCat.{u})

/-- The termwise scalar-sections comparison.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def coefficientComplexSectionsRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    coefficientComplexSections S ≅
      coefficientComplexRestriction a ⋙ coefficientComplexSections R :=
  (Functor.mapHomologicalComplexCompIso (coefficientSectionsRestriction a) (.up ℤ)).symm

/-- A universe-sized presentation of the one-object site for Set.
Source: Stacks Project, sites.tex, Tag 00X9
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
abbrev sectionsPoint : Type u := Discrete PUnit.{u + 1}

/-- The topology with only the maximal covering sieve on the one-object site.
Source: Stacks Project, sites.tex, Tag 00X9
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def sectionsPointTopology : GrothendieckTopology sectionsPoint.{u} := ⊥

/-- The constant integer ring sheaf on the point, lifted to the coefficient universe.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def sectionsPointIntegers : Sheaf sectionsPointTopology CommRingCat.{u} :=
  ⟨(Functor.const sectionsPointᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ)),
    Presheaf.isSheaf_bot _⟩

/-- The existing evaluation equivalence's functor, followed by forgetting integer scalars.
Source: Stacks Project, sites.tex, Tag 00X9; sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
abbrev sectionsPointAbelian :
    coefficientModules sectionsPointIntegers ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation _ (op (Discrete.mk PUnit.unit)) ⋙
    forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}

/-- Evaluation of a sheaf of sets at the only point of the singleton site.
Source: Stacks Project, sites.tex, Tag 00X9
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
abbrev sectionsPointSets : Sheaf sectionsPointTopology (Type u) ⥤ Type u :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (Discrete.mk PUnit.unit))

/-- The global-sections ringed-topos morphism, with its pinned integer structural map.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence). -/
def CoefficientSectionsGeometry (R : Sheaf J CommRingCat.{u}) : Prop :=
      ∃ (g : RingedToposMorphism
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
          ((sheafCompose sectionsPointTopology
            (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers))
        (e : g.inverse ≅ sectionsPointSets ⋙ constantSheaf J (Type u)),
        Nonempty (g.direct ⋙ sectionsPointSets ≅ Sheaf.Γ J (Type u)) ∧
        Nonempty (g.modules ⋙ sectionsPointAbelian ≅ coefficientSections R) ∧
        ∀ (U : Cᵒᵖ) (n : ULift.{u} ℤ),
          g.ringMap.hom.app U
            ((e.inv.app ((sheafCompose sectionsPointTopology (forget RingCat.{u})).obj
              ((sheafCompose sectionsPointTopology
                (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers))).hom.app U
                  ((toSheafify J ((Functor.const Cᵒᵖ).obj (ULift.{u} ℤ))).app U n)) =
                    (n.down : R.obj.obj U)

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private def punctualEquiv : Sheaf sectionsPointTopology.{u} (Type u) ≌ Type u :=
  (sheafBotEquivalence _).trans
    ((Discrete.opposite PUnit.{u + 1}).congrLeft.trans (Functor.equiv (C := Type u)))

private def geometricAdjunction :
    (sectionsPointSets ⋙ constantSheaf J (Type u)) ⊣
      (Sheaf.Γ J (Type u) ⋙ punctualEquiv.inverse) :=
  punctualEquiv.toAdjunction.comp (constantSheafΓAdj J (Type u))

private def integerMap (R : Sheaf J CommRingCat.{u}) :
    (constantSheaf J (Type u)).obj (ULift.{u} ℤ) ⟶
      (sheafCompose J (forget CommRingCat)).obj R :=
  ⟨sheafifyLift J
    { app := fun U ↦ ↾fun n ↦ (n.down : R.obj.obj U)
      naturality := by intro U V f; ext n; exact (map_intCast (R.obj.map f).hom n.down).symm }
    ((sheafCompose J (forget CommRingCat)).obj R).property⟩

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem integerMap_unit (R : Sheaf J CommRingCat.{u})
    (U : Cᵒᵖ) (n : ULift.{u} ℤ) :
    (integerMap R).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (ULift.{u} ℤ))).app U n) =
        (n.down : R.obj.obj U) := by
  have h := toSheafify_sheafifyLift J
    (show (Functor.const Cᵒᵖ).obj (ULift.{u} ℤ) ⟶
      ((sheafCompose J (forget CommRingCat)).obj R).obj from
      { app := fun V ↦ ↾fun m ↦ (m.down : R.obj.obj V)
        naturality := by intro V W f; ext m; exact (map_intCast (R.obj.map f).hom m.down).symm })
    ((sheafCompose J (forget CommRingCat)).obj R).property
  exact congrArg (fun f ↦ f.app U n) h

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem constant_hom_ext {X : Type u} {F : Sheaf J (Type u)}
    {f g : (constantSheaf J (Type u)).obj X ⟶ F}
    (h : ∀ (U : Cᵒᵖ) (x : X),
      f.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app U x) =
        g.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app U x)) : f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.property
  ext U x
  exact h U x

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem constant_map_unit {X Y : Type u} (f : X ⟶ Y) (U : Cᵒᵖ) (x : X) :
    ((constantSheaf J (Type u)).map f).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app U x) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj Y)).app U (f x) :=
  (congrArg (fun f ↦ f.app U x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f))).symm

private instance (R : Sheaf J CommRingCat.{u}) (U : Cᵒᵖ) :
    CommRing (((sheafCompose J (forget CommRingCat)).obj R).obj.obj U) :=
  inferInstanceAs (CommRing (R.obj.obj U))

attribute [local irreducible] integerMap geometricAdjunction

private def sectionsRingData (R : Sheaf J CommRingCat.{u}) :
    RingedToposMorphism.RingData
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
      ((sheafCompose sectionsPointTopology.{u} (forget₂ CommRingCat.{u} RingCat.{u})).obj
        sectionsPointIntegers) where
  inverse := sectionsPointSets ⋙ constantSheaf J (Type u)
  direct := Sheaf.Γ J (Type u) ⋙ punctualEquiv.inverse
  adj := geometricAdjunction
  leftExact := by
    have : PreservesFiniteLimits sectionsPointSets :=
      inferInstanceAs (PreservesFiniteLimits punctualEquiv.functor)
    have : PreservesFiniteLimits (constantSheaf J (Type u)) := by
      unfold constantSheaf
      exact comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  ringMap := integerMap R
  ring_zero := by
    intro T z hz U t
    let zR := RingedToposMorphism.RingData.zero
      (B := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      ((sectionsPointSets ⋙ constantSheaf J (Type u)).obj T)
    have he : (sectionsPointSets ⋙ constantSheaf J (Type u)).map z ≫ integerMap R = zR := by
      apply constant_hom_ext
      intro V x
      change (integerMap R).hom.app V
        (((constantSheaf J (Type u)).map (z.hom.app _)).hom.app V _) = 0
      erw [constant_map_unit, integerMap_unit]
      rw [hz]
      exact Int.cast_zero
    exact congrArg (fun f ↦ f.hom.app U t) he
  ring_one := by
    intro T z hz U t
    let zR := RingedToposMorphism.RingData.one
      (B := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      ((sectionsPointSets ⋙ constantSheaf J (Type u)).obj T)
    have he : (sectionsPointSets ⋙ constantSheaf J (Type u)).map z ≫ integerMap R = zR := by
      apply constant_hom_ext
      intro V x
      change (integerMap R).hom.app V
        (((constantSheaf J (Type u)).map (z.hom.app _)).hom.app V _) = 1
      erw [constant_map_unit, integerMap_unit]
      rw [hz]
      exact Int.cast_one
    exact congrArg (fun f ↦ f.hom.app U t) he
  ring_add := by
    intro T x y z hz U t
    let F := sectionsPointSets ⋙ constantSheaf J (Type u)
    let xR := F.map x ≫ integerMap R
    let yR := F.map y ≫ integerMap R
    let zR := RingedToposMorphism.RingData.add
      (B := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) xR yR
    have he : F.map z ≫ integerMap R = zR := by
      apply constant_hom_ext
      intro V q
      change (integerMap R).hom.app V
          (((constantSheaf J (Type u)).map (z.hom.app _)).hom.app V _) =
        (integerMap R).hom.app V
          (((constantSheaf J (Type u)).map (x.hom.app _)).hom.app V _) +
        (integerMap R).hom.app V
          (((constantSheaf J (Type u)).map (y.hom.app _)).hom.app V _)
      erw [constant_map_unit, constant_map_unit, constant_map_unit,
        integerMap_unit, integerMap_unit, integerMap_unit, hz]
      exact Int.cast_add _ _
    exact congrArg (fun f ↦ f.hom.app U t) he
  ring_mul := by
    intro T x y z hz U t
    let F := sectionsPointSets ⋙ constantSheaf J (Type u)
    let xR := F.map x ≫ integerMap R
    let yR := F.map y ≫ integerMap R
    let zR := RingedToposMorphism.RingData.mul
      (B := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) xR yR
    have he : F.map z ≫ integerMap R = zR := by
      apply constant_hom_ext
      intro V q
      change (integerMap R).hom.app V
          (((constantSheaf J (Type u)).map (z.hom.app _)).hom.app V _) =
        (integerMap R).hom.app V
          (((constantSheaf J (Type u)).map (x.hom.app _)).hom.app V _) *
        (integerMap R).hom.app V
          (((constantSheaf J (Type u)).map (y.hom.app _)).hom.app V _)
      erw [constant_map_unit, constant_map_unit, constant_map_unit,
        integerMap_unit, integerMap_unit, integerMap_unit, hz]
      exact Int.cast_mul _ _
    exact congrArg (fun f ↦ f.hom.app U t) he

private def additiveLift {A : Type u} [Category.{v} A] [Preadditive A]
    [HasBinaryBiproducts A] (F G : A ⥤ AddCommGrpCat) [F.Additive] [G.Additive]
    (α : F ⋙ forget _ ⟶ G ⋙ forget _) : F ⟶ G where
  app M := AddCommGrpCat.ofHom (AddMonoidHom.mk' (α.app M) (by
    intro x y
    let t : F.obj (M ⊞ M) := F.map biprod.inl x + F.map biprod.inr y
    have hf : F.map biprod.fst t = x := by
      simp [t, ← ConcreteCategory.comp_apply, ← F.map_comp]
    have hs : F.map biprod.snd t = y := by
      simp [t, ← ConcreteCategory.comp_apply, ← F.map_comp]
    have hn := ConcreteCategory.congr_hom (α.naturality (biprod.fst + biprod.snd : M ⊞ M ⟶ M)) t
    change α.app M (F.map (biprod.fst + biprod.snd) t) =
      G.map (biprod.fst + biprod.snd) (α.app (M ⊞ M) t) at hn
    rw [F.map_add, G.map_add] at hn
    change α.app M (F.map biprod.fst t + F.map biprod.snd t) =
      G.map biprod.fst (α.app (M ⊞ M) t) + G.map biprod.snd (α.app (M ⊞ M) t) at hn
    rw [hf, hs] at hn
    have hfn := ConcreteCategory.congr_hom
      (α.naturality (biprod.fst : M ⊞ M ⟶ M)) t
    have hsn := ConcreteCategory.congr_hom
      (α.naturality (biprod.snd : M ⊞ M ⟶ M)) t
    change α.app M (F.map biprod.fst t) = G.map biprod.fst (α.app (M ⊞ M) t) at hfn
    change α.app M (F.map biprod.snd t) = G.map biprod.snd (α.app (M ⊞ M) t) at hsn
    rw [hf] at hfn
    rw [hs] at hsn
    exact hn.trans (congrArg₂ (· + ·) hfn.symm hsn.symm)))
  naturality M N f := by
    ext x
    exact ConcreteCategory.congr_hom (α.naturality f) x

private def gammaForget :
    Sheaf.Γ J AddCommGrpCat.{u} ⋙ forget AddCommGrpCat ≅
      sheafCompose J (forget AddCommGrpCat) ⋙ Sheaf.Γ J (Type u) :=
  Functor.isoWhiskerRight (Sheaf.ΓNatIsoLim J AddCommGrpCat) (forget _) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat)
      (preservesLimitNatIso (forget AddCommGrpCat)) ≪≫
    Functor.isoWhiskerLeft (sheafCompose J (forget AddCommGrpCat))
      (Sheaf.ΓNatIsoLim J (Type u)).symm

private def punctualCounit :
    punctualEquiv.inverse ⋙ sectionsPointSets ≅ 𝟭 (Type u) := punctualEquiv.counitIso

private def additiveIso {A : Type*} [Category* A] [Preadditive A]
    [HasBinaryBiproducts A] (F G : A ⥤ AddCommGrpCat.{u}) [F.Additive] [G.Additive]
    (e : F ⋙ forget _ ≅ G ⋙ forget _) : F ≅ G where
  hom := additiveLift F G e.hom
  inv := additiveLift G F e.inv
  hom_inv_id := by
    ext M x
    exact ConcreteCategory.congr_hom (congr_app e.hom_inv_id M) x
  inv_hom_id := by
    ext M x
    exact ConcreteCategory.congr_hom (congr_app e.inv_hom_id M) x

private def modulesComparison (R : Sheaf J CommRingCat.{u})
    (m : (sectionsRingData R).Modules) :
    m.modules ⋙ sectionsPointAbelian.{u} ≅ coefficientSections R := by
  let _ := m.additive
  let _ := coefficientSections_additive R
  have : (m.modules ⋙ sectionsPointAbelian.{u}).Additive := {
    map_add := by
      intro M N f g
      change sectionsPointAbelian.{u}.map (m.modules.map (f + g)) = _
      rw [m.additive.map_add]
      rfl }
  apply additiveIso
  exact Functor.isoWhiskerRight m.underlying sectionsPointSets ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.toSheaf _ ⋙ sheafCompose J (forget AddCommGrpCat))
      (Functor.isoWhiskerLeft (Sheaf.Γ J (Type u)) punctualCounit) ≪≫
    (Functor.isoWhiskerLeft (SheafOfModules.toSheaf _) gammaForget).symm

private theorem geometricExists (R : Sheaf J CommRingCat.{u}) :
    CoefficientSectionsGeometry R := by
  obtain ⟨m⟩ := SheafOfModules.ringData_inducedModules R sectionsPointIntegers
    (sectionsRingData R)
  refine ⟨(sectionsRingData R).withModules m, Iso.refl _,
    ⟨Functor.isoWhiskerLeft (Sheaf.Γ J (Type u)) punctualCounit⟩,
    ⟨modulesComparison R m⟩, ?_⟩
  exact integerMap_unit R

private instance pointAbelianLimits : PreservesFiniteLimits sectionsPointAbelian.{u} := by
  let B := (sheafCompose sectionsPointTopology.{u}
    (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers
  exact inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.evaluation B (op (Discrete.mk PUnit.unit)) ⋙
      forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}))

private instance pointAbelianColimits : PreservesFiniteColimits sectionsPointAbelian.{u} := by
  let B := (sheafCompose sectionsPointTopology.{u}
    (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers
  have hcol : PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} B) := by
    exact ⟨fun {K} _ ↦ ((moduleSheaves_colimits_forgetful _).2.2.2.2.2 K).2.1⟩
  let E := (sheafBotEquivalence (C := sectionsPoint.{u}) AddCommGrpCat.{u}).functor
  have : PreservesFiniteColimits E := inferInstance
  exact inferInstanceAs (PreservesFiniteColimits
    (SheafOfModules.toSheaf B ⋙ E ⋙ (evaluation _ _).obj (op (Discrete.mk PUnit.unit))))

private theorem transportMappedQuasiIso
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    (F : A ⥤ B) (G : B ⥤ E) (H : A ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ⋙ G ≅ H) {I K : CochainComplex A ℤ} (j : I ⟶ K)
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map j)] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map j) := by
  have hq : QuasiIso (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map j) :=
    inferInstanceAs (QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map j)))
  let t := NatIso.mapHomologicalComplex e (.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (t.app _) (t.app _) (t.hom.naturality j).symm)).mp hq

private theorem sections_quasiIso {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : CochainComplex (coefficientModules S) ℤ) (hI : I.IsKInjective)
    (K : CochainComplex (coefficientModules R) ℤ) (hK : K.IsKInjective)
    (j : (coefficientComplexRestriction a).obj I ⟶ K) [QuasiIso j] :
    QuasiIso ((coefficientComplexSections R).map j) := by
  let _ := coefficientSections_additive R
  have : (show SheafOfModules.{u}
      ((sheafCompose sectionsPointTopology.{u}
        (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers) ⥤
      AddCommGrpCat.{u} from sectionsPointAbelian.{u}).Additive :=
    { map_add := by intros; rfl }
  obtain ⟨g, e0, hg, ⟨eg⟩, hring⟩ := geometricExists R
  obtain ⟨f, hf⟩ := restrictionRingedToposModuleDirectImage_exists
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      ((sheafCompose sectionsPointTopology.{u}
        (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers)) :=
    HasDerivedCategory.standard _
  obtain ⟨Rf, Rg, Rgf, ηf, ηg, ηgf, hf', hg', hgf', hi', ht', κ, hκ, _⟩ :=
    ringedToposDerivedPushforwardComposition.{u, u + 1} J J sectionsPointTopology.{u}
      S R sectionsPointIntegers f g
  let ef := NatIso.mapHomologicalComplex (eqToIso hf) (.up ℤ)
  let j' := ef.hom.app I ≫ j
  have hj' : QuasiIso j' := inferInstance
  have hj : QuasiIso ((g.modules.mapHomologicalComplex (.up ℤ)).map j') :=
    (hκ.2 I hI K hK j').1
  have hj0 : QuasiIso ((g.modules.mapHomologicalComplex (.up ℤ)).map j) := by
    have hcomp : QuasiIso ((g.modules.mapHomologicalComplex (.up ℤ)).map (ef.hom.app I) ≫
        (g.modules.mapHomologicalComplex (.up ℤ)).map j) := by
      simpa only [j', Functor.map_comp] using hj
    exact (quasiIso_iff_comp_left _ _).mp hcomp
  let _ := hj0
  exact transportMappedQuasiIso g.modules sectionsPointAbelian (coefficientSections R) eg j

private theorem limitsViaForget {A B E : Type*}
    [Category A] [Category B] [Category E]
    (F : A ⥤ B) (U : A ⥤ E) (V : B ⥤ E) (e : F ⋙ V ≅ U)
    [PreservesFiniteLimits U] [ReflectsFiniteLimits V] : PreservesFiniteLimits F := by
  have : PreservesFiniteLimits (F ⋙ V) := preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves F V

private theorem colimitsViaForget {A B E : Type*}
    [Category A] [Category B] [Category E]
    (F : A ⥤ B) (U : A ⥤ E) (V : B ⥤ E) (e : F ⋙ V ≅ U)
    [PreservesFiniteColimits U] [ReflectsFiniteColimits V] : PreservesFiniteColimits F := by
  have : PreservesFiniteColimits (F ⋙ V) := preservesFiniteColimits_of_natIso e.symm
  exact preservesFiniteColimits_of_reflects_of_preserves F V

private instance restrictionLimits {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    PreservesFiniteLimits (coefficientRestriction a) := by
  have : ReflectsFiniteLimits (SheafOfModules.toSheaf.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  exact limitsViaForget (coefficientRestriction a)
    (SheafOfModules.toSheaf.{u} _) (SheafOfModules.toSheaf.{u} _)
    (coefficientRestrictionForget a)

private instance restrictionColimits {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    PreservesFiniteColimits (coefficientRestriction a) := by
  have hcol (T : Sheaf J CommRingCat.{u}) :
      PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T)) := by
    exact ⟨fun {K} _ ↦ ((moduleSheaves_colimits_forgetful _).2.2.2.2.2 K).2.1⟩
  let _ := hcol R
  let _ := hcol S
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    reflectsFiniteColimitsOfReflectsIsomorphisms _
  exact colimitsViaForget (coefficientRestriction a)
    (SheafOfModules.toSheaf.{u} _) (SheafOfModules.toSheaf.{u} _)
    (coefficientRestrictionForget a)

private def restrictionDerived {R S : Sheaf J CommRingCat.{u}}
    [HasDerivedCategory.{w} (coefficientModules R)]
    [HasDerivedCategory.{w} (coefficientModules S)] (a : R ⟶ S) :
    DerivedCategory (coefficientModules S) ⥤ DerivedCategory (coefficientModules R) :=
  (coefficientRestriction a).mapDerivedCategory

private def restrictionDerivedFactors {R S : Sheaf J CommRingCat.{u}}
    [HasDerivedCategory.{w} (coefficientModules R)]
    [HasDerivedCategory.{w} (coefficientModules S)] (a : R ⟶ S) :
    DerivedCategory.Q ⋙ restrictionDerived a ≅
      coefficientComplexRestriction a ⋙ DerivedCategory.Q :=
  (coefficientRestriction a).mapDerivedCategoryFactors

attribute [local irreducible] restrictionDerived restrictionDerivedFactors

private theorem sectionsDerived_exists (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (coefficientModules R)]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] :
    ∃ (H : DerivedCategory (coefficientModules R) ⥤ DerivedCategory AddCommGrpCat.{u})
      (η : coefficientComplexSections R ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ H),
      H.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso (coefficientModules R) (ComplexShape.up ℤ)) ∧
      ∀ I : CochainComplex (coefficientModules R) ℤ, I.IsKInjective → IsIso (η.app I) := by
  have : IsGrothendieckAbelian.{u} (coefficientModules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses J R).1
  unfold coefficientComplexSections
  exact exists_derived (coefficientSections R)

end

private theorem complex_transport_comp
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive E]
    (a : B ⥤ A) (b : C ⥤ B) (ab : C ⥤ A)
    [a.Additive] [b.Additive] [ab.Additive]
    (FA : A ⥤ E) (FB : B ⥤ E) (FC : C ⥤ E)
    [FA.Additive] [FB.Additive] [FC.Additive]
    (e : b ⋙ a ≅ ab) (ta : a ⋙ FA ≅ FB) (tb : b ⋙ FB ≅ FC)
    (tab : ab ⋙ FA ≅ FC)
    (ht : tb.inv ≫ Functor.whiskerLeft b ta.inv ≫
      Functor.whiskerRight e.hom FA = tab.inv) :
    (NatIso.mapHomologicalComplex tb (.up ℤ)).inv ≫
      Functor.whiskerLeft (b.mapHomologicalComplex (.up ℤ))
        (NatIso.mapHomologicalComplex ta (.up ℤ)).inv ≫
      Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom
        (FA.mapHomologicalComplex (.up ℤ)) =
      (NatIso.mapHomologicalComplex tab (.up ℤ)).inv := by
  ext M i
  exact congr_app ht (M.X i)

private theorem complex_transport_id
    {A E : Type*} [Category A] [Category E] [Preadditive A] [Preadditive E]
    (a : A ⥤ A) [a.Additive] (F : A ⥤ E) [F.Additive]
    (e : a ≅ 𝟭 A) (t : a ⋙ F ≅ F)
    (ht : t.inv = Functor.whiskerRight e.inv F) :
    (NatIso.mapHomologicalComplex t (.up ℤ)).inv =
      Functor.whiskerRight
        (NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv
        (F.mapHomologicalComplex (.up ℤ)) := by
  ext M i
  simpa using congr_app ht (M.X i)

private theorem whisker_transport_comp
    {A B C E Z : Type*} [Category A] [Category B] [Category C] [Category E]
    [Category Z] (a : B ⥤ A) (b : C ⥤ B) (ab : C ⥤ A)
    (FA : A ⥤ E) (FB : B ⥤ E) (FC : C ⥤ E)
    (e : b ⋙ a ≅ ab) (ta : a ⋙ FA ≅ FB) (tb : b ⋙ FB ≅ FC)
    (tab : ab ⋙ FA ≅ FC)
    (ht : tb.inv ≫ Functor.whiskerLeft b ta.inv ≫
      Functor.whiskerRight e.hom FA = tab.inv) (G : E ⥤ Z) :
    Functor.whiskerRight tb.inv G ≫
      Functor.whiskerLeft b (Functor.whiskerRight ta.inv G) ≫
      Functor.whiskerRight e.hom (FA ⋙ G) = Functor.whiskerRight tab.inv G := by
  ext M
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.map_comp] using congrArg G.map (congr_app ht M)

private theorem whisker_transport_id
    {A E Z : Type*} [Category A] [Category E] [Category Z]
    (a : A ⥤ A) (F : A ⥤ E) (e : a ≅ 𝟭 A) (t : a ⋙ F ≅ F)
    (ht : t.inv = Functor.whiskerRight e.inv F) (G : E ⥤ Z) :
    Functor.whiskerRight t.inv G = Functor.whiskerRight e.inv (F ⋙ G) := by
  rw [ht]
  rfl

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem forgettingRestriction_comp
    {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) :
    (coefficientRestrictionForget b).inv ≫
      Functor.whiskerLeft (coefficientRestriction b) (coefficientRestrictionForget a).inv ≫
      Functor.whiskerRight (coefficientRestrictionComp a b).hom
        (SheafOfModules.toSheaf.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) =
      (coefficientRestrictionForget (a ≫ b)).inv := by
  ext M
  rfl

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem forgettingRestriction_id (R : Sheaf J CommRingCat.{u}) :
    (coefficientRestrictionForget (𝟙 R)).inv =
      Functor.whiskerRight (coefficientRestrictionId R).inv
        (SheafOfModules.toSheaf.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) := by
  ext M
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem underivedSections_comp
    {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) :
    (coefficientSectionsRestriction b).inv ≫
      Functor.whiskerLeft (coefficientRestriction b) (coefficientSectionsRestriction a).inv ≫
      Functor.whiskerRight (coefficientRestrictionComp a b).hom (coefficientSections R) =
      (coefficientSectionsRestriction (a ≫ b)).inv :=
  whisker_transport_comp (coefficientRestriction a) (coefficientRestriction b)
    (coefficientRestriction (a ≫ b)) (SheafOfModules.toSheaf _)
    (SheafOfModules.toSheaf _) (SheafOfModules.toSheaf _)
    (coefficientRestrictionComp a b) (coefficientRestrictionForget a)
    (coefficientRestrictionForget b) (coefficientRestrictionForget (a ≫ b))
    (forgettingRestriction_comp a b) (Sheaf.Γ J AddCommGrpCat.{u})

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem underivedSections_id (R : Sheaf J CommRingCat.{u}) :
    (coefficientSectionsRestriction (𝟙 R)).inv =
      Functor.whiskerRight (coefficientRestrictionId R).inv (coefficientSections R) :=
  whisker_transport_id (coefficientRestriction (𝟙 R)) (SheafOfModules.toSheaf _)
    (coefficientRestrictionId R) (coefficientRestrictionForget (𝟙 R))
    (forgettingRestriction_id R) (Sheaf.Γ J AddCommGrpCat.{u})

section
attribute [local irreducible] coefficientSections

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem sectionsRestriction_comp
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) :
    Functor.whiskerRight (coefficientComplexSectionsRestriction b).hom DerivedCategory.Q ≫
      Functor.whiskerLeft (coefficientComplexRestriction b)
        (Functor.whiskerRight (coefficientComplexSectionsRestriction a).hom
          DerivedCategory.Q) ≫
      Functor.whiskerRight (coefficientComplexRestrictionComp a b).hom
        (coefficientComplexSections R ⋙ DerivedCategory.Q) =
      Functor.whiskerRight (coefficientComplexSectionsRestriction (a ≫ b)).hom
        DerivedCategory.Q := by
  exact whisker_transport_comp
    (coefficientComplexRestriction a) (coefficientComplexRestriction b)
    (coefficientComplexRestriction (a ≫ b))
    ((coefficientSections R).mapHomologicalComplex (.up ℤ))
    ((coefficientSections S).mapHomologicalComplex (.up ℤ))
    ((coefficientSections T).mapHomologicalComplex (.up ℤ))
    (coefficientComplexRestrictionComp a b)
    (NatIso.mapHomologicalComplex (coefficientSectionsRestriction a) (.up ℤ))
    (NatIso.mapHomologicalComplex (coefficientSectionsRestriction b) (.up ℤ))
    (NatIso.mapHomologicalComplex (coefficientSectionsRestriction (a ≫ b)) (.up ℤ))
    (complex_transport_comp (coefficientRestriction a) (coefficientRestriction b)
      (coefficientRestriction (a ≫ b)) (coefficientSections R)
      (coefficientSections S) (coefficientSections T)
      (coefficientRestrictionComp a b) (coefficientSectionsRestriction a)
      (coefficientSectionsRestriction b) (coefficientSectionsRestriction (a ≫ b))
      (underivedSections_comp a b)) DerivedCategory.Q

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem sectionsRestriction_id
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] (R : Sheaf J CommRingCat.{u}) :
    Functor.whiskerRight (coefficientComplexSectionsRestriction (𝟙 R)).hom
      DerivedCategory.Q =
      Functor.whiskerRight (coefficientComplexRestrictionId R).inv
        (coefficientComplexSections R ⋙ DerivedCategory.Q) := by
  exact whisker_transport_id (coefficientComplexRestriction (𝟙 R))
    ((coefficientSections R).mapHomologicalComplex (.up ℤ))
    (coefficientComplexRestrictionId R)
    (NatIso.mapHomologicalComplex (coefficientSectionsRestriction (𝟙 R)) (.up ℤ))
    (complex_transport_id (coefficientRestriction (𝟙 R)) (coefficientSections R)
      (coefficientRestrictionId R) (coefficientSectionsRestriction (𝟙 R))
      (underivedSections_id R)) DerivedCategory.Q

end

section
private theorem comparison_isIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{u} A] [IsGrothendieckAbelian.{u} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    (F : CochainComplex B ℤ ⥤ CochainComplex A ℤ)
    (G : CochainComplex A ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (HS : DerivedCategory (B) ⥤ DerivedCategory AddCommGrpCat.{u})
    (HR : DerivedCategory (A) ⥤ DerivedCategory AddCommGrpCat.{u})
    (GS : CochainComplex B ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (e : GS ≅ F ⋙ G)
    (ηS : GS ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ HS)
    (ηR : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ HR)
    (hηS : ∀ I : CochainComplex (B) ℤ,
      I.IsKInjective → IsIso (ηS.app I))
    (hηR : ∀ I : CochainComplex (A) ℤ,
      I.IsKInjective → IsIso (ηR.app I))
    (r : DerivedCategory (B) ⥤ DerivedCategory (A))
    (ν : DerivedCategory.Q ⋙ r ≅ F ⋙ DerivedCategory.Q)
    (σ : HS ⟶ r ⋙ HR)
    (hσ : ∀ M : CochainComplex (B) ℤ,
      ηS.app M ≫ σ.app (DerivedCategory.Q.obj M) =
        DerivedCategory.Q.map (e.hom.app M) ≫
          ηR.app (F.obj M) ≫ HR.map (ν.inv.app M))
    (hγ : ∀ (I : CochainComplex (B) ℤ), I.IsKInjective →
      ∀ (K : CochainComplex (A) ℤ), K.IsKInjective →
      ∀ (j : (F).obj I ⟶ K), ∀ [QuasiIso j],
      QuasiIso ((G).map j)) : IsIso σ := by
  have hKI (I : CochainComplex (B) ℤ) (hI : I.IsKInjective) :
      IsIso (σ.app (DerivedCategory.Q.obj I)) := by
    obtain ⟨K, hK, j, _, hj⟩ :=
      Abelian.HasKInjectiveResolutions.exists_isKInjective ((F).obj I)
    let _ := hγ I hI K hK j
    have hn := ηR.naturality j
    change DerivedCategory.Q.map ((G).map j) ≫ ηR.app K =
      ηR.app ((F).obj I) ≫ HR.map (DerivedCategory.Q.map j) at hn
    have : IsIso (ηR.app K) := hηR K hK
    have : IsIso (ηS.app I) := hηS I hI
    have : IsIso (ηR.app ((F).obj I) ≫
        HR.map (DerivedCategory.Q.map j)) := by
      rw [← hn]
      infer_instance
    have : IsIso (ηR.app ((F).obj I)) :=
      (isIso_comp_right_iff _ (HR.map (DerivedCategory.Q.map j))).mp inferInstance
    have : IsIso (ηS.app I ≫ σ.app (DerivedCategory.Q.obj I)) := by
      rw [hσ]
      infer_instance
    exact (isIso_comp_left_iff (ηS.app I) _).mp inferInstance
  have (X : DerivedCategory (B)) : IsIso (σ.app X) := by
    obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
    let _ := hKI I hI
    have : IsIso (σ.app X ≫ (r ⋙ HR).map e.hom) := by
      rw [← σ.naturality]
      infer_instance
    exact (isIso_comp_right_iff _ ((r ⋙ HR).map e.hom)).mp inferInstance
  exact NatIso.isIso_of_isIso_app _

private theorem normalizedDesc_exists
    {A D E : Type*} [Category A] [Category D] [Category E]
    (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (F : A ⥤ E) (H : D ⥤ E) (η : F ⟶ Q ⋙ H)
    (hH : H.IsRightDerivedFunctor η W) (G : D ⥤ E) (β : F ⟶ Q ⋙ G) :
    ∃ σ : H ⟶ G, ∀ M, η.app M ≫ σ.app (Q.obj M) = β.app M := by
  have := hH
  exact ⟨H.rightDerivedDesc η W G β, Functor.rightDerived_fac_app H η W G β⟩

private theorem normalizedComparison_exists
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{u} A] [IsGrothendieckAbelian.{u} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    (F : CochainComplex B ℤ ⥤ CochainComplex A ℤ)
    (G : CochainComplex A ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (HS : DerivedCategory (B) ⥤ DerivedCategory AddCommGrpCat.{u})
    (HR : DerivedCategory (A) ⥤ DerivedCategory AddCommGrpCat.{u})
    (GS : CochainComplex B ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (e : GS ≅ F ⋙ G)
    (ηS : GS ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ HS)
    (ηR : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ HR)
    (hηS : ∀ I : CochainComplex (B) ℤ,
      I.IsKInjective → IsIso (ηS.app I))
    (hηR : ∀ I : CochainComplex (A) ℤ,
      I.IsKInjective → IsIso (ηR.app I))
    [HS.IsRightDerivedFunctor ηS
      (HomologicalComplex.quasiIso (B) (.up ℤ))]
    (r : DerivedCategory (B) ⥤ DerivedCategory (A))
    (ν : DerivedCategory.Q ⋙ r ≅ F ⋙ DerivedCategory.Q)
    (hγ : ∀ (I : CochainComplex B ℤ), I.IsKInjective →
      ∀ (K : CochainComplex A ℤ), K.IsKInjective →
      ∀ (j : F.obj I ⟶ K), ∀ [QuasiIso j], QuasiIso (G.map j)) :
    ∃ σ : HS ⟶ r ⋙ HR, IsIso σ ∧
      (∀ M : CochainComplex (B) ℤ,
        ηS.app M ≫ σ.app (DerivedCategory.Q.obj M) =
          DerivedCategory.Q.map (e.hom.app M) ≫
          ηR.app (F.obj M) ≫ HR.map (ν.inv.app M)) ∧
      (∀ τ : HS ⟶ r ⋙ HR,
        (∀ M : CochainComplex (B) ℤ,
          ηS.app M ≫ τ.app (DerivedCategory.Q.obj M) =
            DerivedCategory.Q.map (e.hom.app M) ≫
          ηR.app (F.obj M) ≫ HR.map (ν.inv.app M)) →
          τ = σ) ∧
      ∀ (I : CochainComplex (B) ℤ), I.IsKInjective →
      ∀ (K : CochainComplex (A) ℤ), K.IsKInjective →
      ∀ (j : (F).obj I ⟶ K), ∀ [QuasiIso j],
        QuasiIso ((G).map j) ∧
        ηS.app I ≫ σ.app (DerivedCategory.Q.obj I) ≫ HR.map (ν.hom.app I) ≫
          HR.map (DerivedCategory.Q.map j) =
            DerivedCategory.Q.map (e.hom.app I) ≫
              DerivedCategory.Q.map (G.map j) ≫ ηR.app K := by
  obtain ⟨σ, hσ⟩ := normalizedDesc_exists DerivedCategory.Q
    (HomologicalComplex.quasiIso (B) (.up ℤ))
    (GS ⋙ DerivedCategory.Q) HS ηS inferInstance (r ⋙ HR)
    (Functor.whiskerRight e.hom DerivedCategory.Q ≫
      Functor.whiskerLeft F ηR ≫ Functor.whiskerRight ν.inv HR)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hσ
  refine ⟨σ, ?_⟩
  refine ⟨comparison_isIso F G HS HR GS e ηS ηR hηS hηR r ν σ hσ hγ,
    hσ, ?_, ?_⟩
  · intro τ hτ
    apply Functor.rightDerived_ext HS ηS
      (HomologicalComplex.quasiIso (B) (.up ℤ))
    apply NatTrans.ext
    funext M
    exact (hτ M).trans (hσ M).symm
  · intro I hI K hK j hj
    refine ⟨hγ I hI K hK j, ?_⟩
    rw [← Category.assoc, ← Category.assoc, hσ]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [Category.id_comp]
    exact congrArg (DerivedCategory.Q.map (e.hom.app I) ≫ ·) (ηR.naturality j).symm

private theorem normalized_composite
    {D E A : Type*} [Category D] [Category E] [Category A]
    (r : D ⥤ E) (H : E ⥤ A) (G : D ⥤ A) (σ : G ⟶ r ⋙ H)
    {x y : D} {z t : E} {p q : A}
    (v : x ≅ y) (w : r.obj y ≅ z) (u : t ≅ z) (c : t ⟶ r.obj x)
    (η : p ⟶ q) (ηG : p ⟶ G.obj y) (ηH : p ⟶ H.obj z)
    (s : q ⟶ H.obj t) (b : q ⟶ G.obj x)
    (hc : c ≫ r.map v.hom ≫ w.hom = u.hom)
    (ha : ηG ≫ σ.app y = ηH ≫ H.map w.inv)
    (hb : η ≫ b = ηG ≫ G.map v.inv)
    (hu : η ≫ s = ηH ≫ H.map u.inv) :
    η ≫ (s ≫ H.map c) = η ≫ (b ≫ σ.app x) := by
  have hc' := hc
  have hinv : u.inv ≫ c = w.inv ≫ r.map v.inv := by
    apply (cancel_mono (r.map v.hom ≫ w.hom)).mp
    simp only [Category.assoc]
    rw [hc']
    simp only [Iso.inv_hom_id, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      Functor.map_id, Category.id_comp]
  rw [← Category.assoc, hu, Category.assoc, ← H.map_comp, hinv]
  rw [← Category.assoc, hb, Category.assoc, σ.naturality]
  dsimp only [Functor.comp_map]
  rw [← Category.assoc, ha]
  simp only [Category.assoc, Functor.map_comp]

private theorem normalizedLift
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (V : C ⥤ E) (F G : D ⥤ E) (e : L ⋙ F ≅ V) (ν : L ⋙ G ≅ V) :
    ∃ c : G ≅ F, ∀ M, c.hom.app (L.obj M) ≫ e.hom.app M = ν.hom.app M := by
  let _ : Localization.Lifting L W V F := ⟨e⟩
  let _ : Localization.Lifting L W V G := ⟨ν⟩
  let c : G ≅ F := Localization.liftNatIso L W V V G F (Iso.refl _)
  refine ⟨c, ?_⟩
  intro M
  simp only [c, Localization.liftNatIso_hom]
  rw [Localization.liftNatTrans_app]
  change (ν.hom.app M ≫ 𝟙 _ ≫ e.inv.app M) ≫ e.hom.app M = _
  simp

private theorem general_coherence
    {A B C DA DB DC E : Type*}
    [Category A] [Category B] [Category C] [Category DA] [Category DB] [Category DC]
    [Category E] (QA : A ⥤ DA) (QB : B ⥤ DB) (QC : C ⥤ DC)
    (W : MorphismProperty C) [QC.IsLocalization W]
    (a : B ⥤ A) (b : C ⥤ B) (FA : A ⥤ E) (FB : B ⥤ E) (FC : C ⥤ E)
    (ta : FB ⟶ a ⋙ FA) (tb : FC ⟶ b ⋙ FB)
    (HA : DA ⥤ E) (HB : DB ⥤ E) (HC : DC ⥤ E)
    (ηA : FA ⟶ QA ⋙ HA) (ηB : FB ⟶ QB ⋙ HB)
    (ηC : FC ⟶ QC ⋙ HC) (hHC : HC.IsRightDerivedFunctor ηC W)
    (ra : DB ⥤ DA) (rb : DC ⥤ DB) (rab : DC ⥤ DA)
    (νa : QB ⋙ ra ≅ a ⋙ QA) (νb : QC ⋙ rb ≅ b ⋙ QB)
    (νab : QC ⋙ rab ≅ b ⋙ a ⋙ QA)
    (σa : HB ⟶ ra ⋙ HA) (σb : HC ⟶ rb ⋙ HB) (σab : HC ⟶ rab ⋙ HA)
    (ha : ∀ M, ηB.app M ≫ σa.app (QB.obj M) = ta.app M ≫ ηA.app (a.obj M) ≫ HA.map (νa.inv.app M))
    (hb : ∀ M, ηC.app M ≫ σb.app (QC.obj M) = tb.app M ≫ ηB.app (b.obj M) ≫ HB.map (νb.inv.app M))
    (hab : ∀ M, ηC.app M ≫ σab.app (QC.obj M) =
      tb.app M ≫ ta.app (b.obj M) ≫ ηA.app (a.obj (b.obj M)) ≫
        HA.map (νab.inv.app M)) :
    ∃ c : rab ≅ rb ⋙ ra,
      (∀ M, c.hom.app (QC.obj M) ≫ ra.map (νb.hom.app M) ≫ νa.hom.app (b.obj M) =
        νab.hom.app M) ∧
      ∀ X, σab.app X ≫ HA.map (c.hom.app X) = σb.app X ≫ σa.app (rb.obj X) := by
  have := hHC
  let e : QC ⋙ rb ⋙ ra ≅ b ⋙ a ⋙ QA :=
    Functor.isoWhiskerRight νb ra ≪≫ Functor.isoWhiskerLeft b νa
  obtain ⟨c, hc⟩ := normalizedLift QC W _ (rb ⋙ ra) rab e νab
  refine ⟨c, hc, ?_⟩
  have heq : σab ≫ Functor.whiskerRight c.hom HA = σb ≫ Functor.whiskerLeft rb σa := by
    apply Functor.rightDerived_ext HC ηC W
    ext M
    exact normalized_composite ra HA HB σa (νb.app M) (νa.app (b.obj M)) (νab.app M)
      (c.hom.app (QC.obj M)) (ηC.app M) (tb.app M ≫ ηB.app (b.obj M))
      (tb.app M ≫ ta.app (b.obj M) ≫ ηA.app (a.obj (b.obj M)))
      (σab.app _) (σb.app _) (hc M) (by
        simp only [Iso.app_inv, Functor.comp_obj]
        simpa only [Category.assoc] using
          congrArg (fun f ↦ tb.app M ≫ f) (ha (b.obj M))) (by
        simpa only [Category.assoc, Iso.app_inv] using hb M) (by
        simpa only [Category.assoc, Iso.app_inv] using hab M)
  exact fun X ↦ congr_app heq X

private theorem transported_coherence
    {A B C DA DB DC E : Type*}
    [Category A] [Category B] [Category C] [Category DA] [Category DB] [Category DC]
    [Category E] (QA : A ⥤ DA) (QB : B ⥤ DB) (QC : C ⥤ DC)
    (W : MorphismProperty C) [QC.IsLocalization W]
    (a : B ⥤ A) (b : C ⥤ B) (ab : C ⥤ A) (ec : b ⋙ a ≅ ab)
    (FA : A ⥤ E) (FB : B ⥤ E) (FC : C ⥤ E)
    (ta : FB ⟶ a ⋙ FA) (tb : FC ⟶ b ⋙ FB) (tab : FC ⟶ ab ⋙ FA)
    (ht : tb ≫ Functor.whiskerLeft b ta ≫ Functor.whiskerRight ec.hom FA = tab)
    (HA : DA ⥤ E) (HB : DB ⥤ E) (HC : DC ⥤ E)
    (ηA : FA ⟶ QA ⋙ HA) (ηB : FB ⟶ QB ⋙ HB)
    (ηC : FC ⟶ QC ⋙ HC) (hHC : HC.IsRightDerivedFunctor ηC W)
    (ra : DB ⥤ DA) (rb : DC ⥤ DB) (rab : DC ⥤ DA)
    (νa : QB ⋙ ra ≅ a ⋙ QA) (νb : QC ⋙ rb ≅ b ⋙ QB)
    (νab : QC ⋙ rab ≅ ab ⋙ QA)
    (σa : HB ⟶ ra ⋙ HA) (σb : HC ⟶ rb ⋙ HB) (σab : HC ⟶ rab ⋙ HA)
    (ha : ∀ M, ηB.app M ≫ σa.app (QB.obj M) =
      ta.app M ≫ ηA.app (a.obj M) ≫ HA.map (νa.inv.app M))
    (hb : ∀ M, ηC.app M ≫ σb.app (QC.obj M) =
      tb.app M ≫ ηB.app (b.obj M) ≫ HB.map (νb.inv.app M))
    (hab : ∀ M, ηC.app M ≫ σab.app (QC.obj M) =
      tab.app M ≫ ηA.app (ab.obj M) ≫ HA.map (νab.inv.app M)) :
    ∃ c : rab ≅ rb ⋙ ra,
      (∀ M, c.hom.app (QC.obj M) ≫ ra.map (νb.hom.app M) ≫
        νa.hom.app (b.obj M) ≫ QA.map (ec.hom.app M) = νab.hom.app M) ∧
      ∀ X, σab.app X ≫ HA.map (c.hom.app X) = σb.app X ≫ σa.app (rb.obj X) := by
  let νab' := νab ≪≫ Functor.isoWhiskerRight ec.symm QA
  have hab' (M : C) : ηC.app M ≫ σab.app (QC.obj M) =
      tb.app M ≫ ta.app (b.obj M) ≫ ηA.app (a.obj (b.obj M)) ≫
        HA.map (νab'.inv.app M) := by
    rw [hab]
    dsimp only [νab', Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
      Iso.symm_inv, Functor.whiskerRight_app]
    rw [Functor.map_comp]
    have hn := ηA.naturality (ec.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    have hn' := congrArg (fun f ↦ f ≫ HA.map (νab.inv.app M)) hn
    simp only [Category.assoc] at hn'
    rw [← hn']
    have h := congr_app ht M
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using
      (congrArg (fun f ↦ f ≫ ηA.app (ab.obj M) ≫ HA.map (νab.inv.app M)) h).symm
  obtain ⟨c, hc, hσ⟩ := general_coherence QA QB QC W a b FA FB FC ta tb
    HA HB HC ηA ηB ηC hHC ra rb rab νa νb νab' σa σb σab ha hb hab'
  refine ⟨c, ?_, hσ⟩
  intro M
  have h := congrArg (fun f ↦ f ≫ QA.map (ec.hom.app M)) (hc M)
  dsimp only [νab', Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, Functor.whiskerRight_app] at h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.map_id] at h
  exact h.trans (Category.comp_id _)

private theorem general_identity
    {A D E : Type*} [Category A] [Category D] [Category E]
    (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (F : A ⥤ E) (H : D ⥤ E) (η : F ⟶ Q ⋙ H) (hH : H.IsRightDerivedFunctor η W)
    (r : D ⥤ D) (ν : Q ⋙ r ≅ Q) (σ : H ⟶ r ⋙ H)
    (hσ : ∀ M, η.app M ≫ σ.app (Q.obj M) = η.app M ≫ H.map (ν.inv.app M)) :
    ∃ i : r ≅ 𝟭 D, (∀ M, i.hom.app (Q.obj M) = ν.hom.app M) ∧
      ∀ X, σ.app X ≫ H.map (i.hom.app X) = 𝟙 (H.obj X) := by
  have := hH
  obtain ⟨i, hi⟩ := normalizedLift Q W Q (𝟭 D) r (Iso.refl _) ν
  have hi' (M : A) : i.hom.app (Q.obj M) = ν.hom.app M := by
    have h := hi M
    change i.hom.app (Q.obj M) ≫ 𝟙 _ = _ at h
    exact (Category.comp_id _).symm.trans h
  refine ⟨i, hi', ?_⟩
  have heq : σ ≫ Functor.whiskerRight i.hom H = 𝟙 H := by
    apply Functor.rightDerived_ext H η W
    ext M
    change η.app M ≫ (σ.app (Q.obj M) ≫ H.map (i.hom.app (Q.obj M))) = η.app M ≫ 𝟙 _
    rw [← Category.assoc, hσ, hi']
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Category.comp_id]
    exact Category.comp_id _
  exact fun X ↦ congr_app heq X

private theorem transported_identity
    {A D E : Type*} [Category A] [Category D] [Category E]
    (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (f : A ⥤ A) (e : f ≅ 𝟭 A) (F : A ⥤ E)
    (t : F ⟶ f ⋙ F) (ht : t = Functor.whiskerRight e.inv F)
    (H : D ⥤ E) (η : F ⟶ Q ⋙ H) (hH : H.IsRightDerivedFunctor η W)
    (r : D ⥤ D) (ν : Q ⋙ r ≅ f ⋙ Q) (σ : H ⟶ r ⋙ H)
    (hσ : ∀ M, η.app M ≫ σ.app (Q.obj M) =
      t.app M ≫ η.app (f.obj M) ≫ H.map (ν.inv.app M)) :
    ∃ i : r ≅ 𝟭 D,
      (∀ M, i.hom.app (Q.obj M) = ν.hom.app M ≫ Q.map (e.hom.app M)) ∧
      ∀ X, σ.app X ≫ H.map (i.hom.app X) = 𝟙 (H.obj X) := by
  let ν' : Q ⋙ r ≅ Q := ν ≪≫ Functor.isoWhiskerRight e Q
  have hs (M : A) : η.app M ≫ σ.app (Q.obj M) =
      η.app M ≫ H.map (ν'.inv.app M) := by
    rw [hσ, ht]
    have hn := η.naturality (e.inv.app M)
    dsimp only [Functor.comp_map] at hn
    dsimp only [ν', Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
      Functor.whiskerRight_app]
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
    rfl
  exact general_identity Q W F H η hH r ν' σ hs

end

section

attribute [local irreducible] coefficientComplexRestriction coefficientComplexSections
  coefficientComplexSectionsRestriction coefficientComplexRestrictionComp
  coefficientComplexRestrictionId

private theorem coefficientGrothendieck (R : Sheaf J CommRingCat.{u}) :
    IsGrothendieckAbelian.{u} (coefficientModules R) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
    J R).1

attribute [local irreducible] restrictionDerived restrictionDerivedFactors
  coefficientRestriction coefficientSections
  CoefficientSectionsGeometry SheafOfModules.instCategory

/-- The unit-normalized scalar comparisons, their resolution formula, and their cocycle.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E
(blueprint: lem-coef-derived-sections-scalar-coherence).

Proof plan:
1. Restriction preserves underlying abelian sheaves, hence kernels, cokernels and
   quasi-isomorphisms. Descend it through Q; its localization factors determine its
   composition and identity comparisons uniquely.
2. The constant-sheaf/global-sections adjunction gives the geometric morphism to Set.
   The map from the constant integer sheaf sends n to n times 1. The singleton-site
   module equivalence identifies its module direct image with coefficientSections.
3. Realize coefficient restriction as a ringed-topos direct image using
   lem-weil-pbc-restriction-ringed-topos-module-direct-image. Apply
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition followed by the morphism
   in step 2. Its representative formula gives the quasi-isomorphism Gamma(j).
4. K-injective resolutions exist by prop-pur-kinjective-resolutions-exist. The
   universal property of def-sfb-right-derived-functor constructs a unique sigma
   carrying the S-derived unit to the R-derived unit, after the localization factors.
5. At a K-injective L, naturality at j identifies sigma with Gamma(j), conjugated by
   the derived units and localization factors. Every factor is invertible by step 3.
   Resolving an arbitrary complex and naturality prove invertibility everywhere.
6. The same formula is precisely the canonical 0D6E composition comparison under
   the singleton-site equivalence; uniqueness makes it independent of all resolutions.
7. Precompose the composite of two sigmas with the T-unit. The unit equation twice
   gives the unit equation for the composite ring map; universal uniqueness gives
   the cocycle. Applying the same argument to the identity gives its normalization.
No flatness or preservation of injectives by restriction is used. -/
theorem derivedSectionsScalarCoherence
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (coefficientModules R)]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] :
    (∀ R : Sheaf J CommRingCat.{u}, CoefficientSectionsGeometry R) ∧
    ∃ (H : ∀ R : Sheaf J CommRingCat.{u},
        DerivedCategory (coefficientModules R) ⥤ DerivedCategory AddCommGrpCat.{u})
      (η : ∀ R : Sheaf J CommRingCat.{u},
        coefficientComplexSections R ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ H R),
      (∀ R : Sheaf J CommRingCat.{u}, (H R).IsRightDerivedFunctor (η R)
        (HomologicalComplex.quasiIso (coefficientModules R) (ComplexShape.up ℤ))) ∧
      (∀ (R : Sheaf J CommRingCat.{u}) (I : CochainComplex (coefficientModules R) ℤ),
        I.IsKInjective → IsIso ((η R).app I)) ∧
      ∃ (r : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) →
          DerivedCategory (coefficientModules S) ⥤ DerivedCategory (coefficientModules R))
        (ν : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S),
          DerivedCategory.Q ⋙ r a ≅ coefficientComplexRestriction a ⋙ DerivedCategory.Q)
        (σ : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), H S ⟶ r a ⋙ H R),
        (∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S),
          IsIso (σ a) ∧
          (∀ M : CochainComplex (coefficientModules S) ℤ,
            (η S).app M ≫ (σ a).app (DerivedCategory.Q.obj M) =
              DerivedCategory.Q.map ((coefficientComplexSectionsRestriction a).hom.app M) ≫
              (η R).app ((coefficientComplexRestriction a).obj M) ≫
                (H R).map ((ν a).inv.app M)) ∧
          (∀ τ : H S ⟶ r a ⋙ H R,
            (∀ M : CochainComplex (coefficientModules S) ℤ,
              (η S).app M ≫ τ.app (DerivedCategory.Q.obj M) =
                DerivedCategory.Q.map ((coefficientComplexSectionsRestriction a).hom.app M) ≫
                  (η R).app ((coefficientComplexRestriction a).obj M) ≫
                  (H R).map ((ν a).inv.app M)) → τ = σ a) ∧
          ∀ (I : CochainComplex (coefficientModules S) ℤ), I.IsKInjective →
          ∀ (K : CochainComplex (coefficientModules R) ℤ), K.IsKInjective →
          ∀ (j : (coefficientComplexRestriction a).obj I ⟶ K), ∀ [QuasiIso j],
            QuasiIso ((coefficientComplexSections R).map j) ∧
            (η S).app I ≫ (σ a).app (DerivedCategory.Q.obj I) ≫
              (H R).map ((ν a).hom.app I) ≫ (H R).map (DerivedCategory.Q.map j) =
                DerivedCategory.Q.map ((coefficientComplexSectionsRestriction a).hom.app I) ≫
                  DerivedCategory.Q.map ((coefficientComplexSections R).map j) ≫
                    (η R).app K) ∧
        (∀ {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T),
          ∃ c : r (a ≫ b) ≅ r b ⋙ r a,
            (∀ M : CochainComplex (coefficientModules T) ℤ,
              c.hom.app (DerivedCategory.Q.obj M) ≫
                (r a).map ((ν b).hom.app M) ≫
                  (ν a).hom.app ((coefficientComplexRestriction b).obj M) ≫
                    DerivedCategory.Q.map ((coefficientComplexRestrictionComp a b).hom.app M) =
                    (ν (a ≫ b)).hom.app M) ∧
            ∀ X : DerivedCategory (coefficientModules T),
              (σ (a ≫ b)).app X ≫ (H R).map (c.hom.app X) =
                (σ b).app X ≫ (σ a).app ((r b).obj X)) ∧
        ∀ R : Sheaf J CommRingCat.{u}, ∃ i : r (𝟙 R) ≅ 𝟭 _,
          (∀ M : CochainComplex (coefficientModules R) ℤ,
            i.hom.app (DerivedCategory.Q.obj M) = (ν (𝟙 R)).hom.app M ≫
              DerivedCategory.Q.map ((coefficientComplexRestrictionId R).hom.app M)) ∧
          ∀ X : DerivedCategory (coefficientModules R),
            (σ (𝟙 R)).app X ≫ (H R).map (i.hom.app X) = 𝟙 ((H R).obj X) := by
  classical
  refine ⟨geometricExists, ?_⟩
  choose H η hH hI using (fun R : Sheaf J CommRingCat.{u} ↦
    sectionsDerived_exists R)
  refine ⟨H, η, hH, hI, ?_⟩
  let r := fun {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) ↦ restrictionDerived a
  let ν := fun {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) ↦ restrictionDerivedFactors a
  have hex (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) := by
    let _ := hH S
    have : IsGrothendieckAbelian.{u} (coefficientModules R) :=
      coefficientGrothendieck R
    have : IsGrothendieckAbelian.{u} (coefficientModules S) :=
      coefficientGrothendieck S
    exact normalizedComparison_exists (coefficientComplexRestriction a)
      (coefficientComplexSections R) (H S) (H R)
      (coefficientComplexSections S) (coefficientComplexSectionsRestriction a)
      (η S) (η R) (hI S) (hI R)
      (r a) (ν a) (sections_quasiIso a)
  choose σ hσ using hex
  refine ⟨r, ν, (fun {R S} a ↦ σ R S a), (fun {R S} a ↦ hσ R S a), ?_⟩
  constructor
  · intro R S T a b
    exact transported_coherence DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      (HomologicalComplex.quasiIso (coefficientModules T) (.up ℤ))
      (coefficientComplexRestriction a) (coefficientComplexRestriction b)
      (coefficientComplexRestriction (a ≫ b)) (coefficientComplexRestrictionComp a b)
      (coefficientComplexSections R ⋙ DerivedCategory.Q)
      (coefficientComplexSections S ⋙ DerivedCategory.Q)
      (coefficientComplexSections T ⋙ DerivedCategory.Q)
      (Functor.whiskerRight (coefficientComplexSectionsRestriction a).hom DerivedCategory.Q)
      (Functor.whiskerRight (coefficientComplexSectionsRestriction b).hom DerivedCategory.Q)
      (Functor.whiskerRight (coefficientComplexSectionsRestriction (a ≫ b)).hom
        DerivedCategory.Q) (sectionsRestriction_comp a b)
      (H R) (H S) (H T) (η R) (η S) (η T) (hH T)
      (r a) (r b) (r (a ≫ b)) (ν a) (ν b) (ν (a ≫ b))
      (σ R S a) (σ S T b) (σ R T (a ≫ b))
      ((hσ R S a).2.1) ((hσ S T b).2.1) ((hσ R T (a ≫ b)).2.1)
  · intro R
    exact transported_identity DerivedCategory.Q
      (HomologicalComplex.quasiIso (coefficientModules R) (.up ℤ))
      (coefficientComplexRestriction (𝟙 R)) (coefficientComplexRestrictionId R)
      (coefficientComplexSections R ⋙ DerivedCategory.Q)
      (Functor.whiskerRight (coefficientComplexSectionsRestriction (𝟙 R)).hom
        DerivedCategory.Q) (sectionsRestriction_id R)
      (H R) (η R) (hH R) (r (𝟙 R)) (ν (𝟙 R)) (σ R R (𝟙 R))
      ((hσ R R (𝟙 R)).2.1)

end

end CategoryTheory.CoefficientDerivedSections
