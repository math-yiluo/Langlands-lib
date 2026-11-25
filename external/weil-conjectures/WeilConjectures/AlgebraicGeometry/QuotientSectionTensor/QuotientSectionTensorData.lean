/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.SectionDerivedTensorNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # Normalized quotient tensors under the section equivalence

The helpers record the representative normalization, the scalar realization data,
and the tensor, pullback and adjunction comparison equations.
`quotient_section_tensor_normalization` is the main statement.

All scalar extensions are total left derived functors. In particular ordinary
extension by the finite quotient is not assumed exact. Natural levels n mean n + 1.

## References

* Stacks 03EK, 03EL and 07A4
* Stacks 03EL, 06YY and 07A4
* Stacks 0D6D, 0G7E, 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- The actual section-ring quotient map, with the site's Hom universe retained. -/
abbrev sectionQuotient (T : Scheme.{u}) :=
  CondensedRing.sectionRingMap T (coefficientMap a T)

/-- A universal sectionwise scalar-extension model from the recorded change-of-rings API. -/
abbrev SectionModel (T : Scheme.{u})
    [HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
    [HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)] :=
  SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 1, u + 1}
    (sectionQuotient a T)

/-- The ordinary scalar-unit normalized tensorator, totalized with the signed differential. -/
def totalScalar (T : Scheme.{u})
    (P Q : CochainComplex (Modules Λ T) ℤ) :
    ((extension a T).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ⟶
      ((extension a T).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((extension a T).mapHomologicalComplex (.up ℤ)).obj Q :=
  letI := CondensedRing.internalScalarMonoidal a T
  HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans (extension a T)) (.up ℤ) P Q

/-- Normalization on every flat-term K-flat pair by the actual localization counits.
The ordinary tensorator is the balancing map (u tensor v) tensor s to
(u tensor 1) tensor (v tensor s), rather than a freely chosen isomorphism. -/
def TensorNormalized (T : Scheme.{u})
    (b : Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙
        D a T ≅
      ((D a T).prod (D a T)) ⋙
        Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T)) : Prop :=
  letI : (DerivedCategory.Q (C := Modules Λ T)).LaxMonoidal := Mod.laxMonoidalQ
  letI : (DerivedCategory.Q (C := Modules Λ' T)).LaxMonoidal := Mod.laxMonoidalQ
  ∀ P Q : CochainComplex (Modules Λ T) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (compute a T P ⊗ₘ compute a T Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj Q) =
        (D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          compute a T (P ⊗ Q) ≫
          DerivedCategory.Q.map (totalScalar a T P Q)

set_option backward.isDefEq.respectTransparency false in
/-- The regular scalar unit localized in degree zero, using multiplication in the quotient. -/
def scalarRegularUnit (T : Scheme.{u}) :
    (D a T).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (𝟙_ (Modules Λ T)))) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (𝟙_ (Modules Λ' T))) :=
  letI := CondensedRing.internalScalarMonoidal a T
  compute a T _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (extension a T) (.up ℤ) 0).hom.app (𝟙_ _)) ≫
    DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map
      (Functor.OplaxMonoidal.η (extension a T)))

open ModuleRingedComparison

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The ordinary and derived scalar comparisons, normalized on section generators and
by the universal localization counits. The target is an actual sectionwise extension
model, so c is a map of quotient-module sheaves, retaining the quotient action. -/
structure ScalarSectionData (T : Scheme.{u}) where
  model : SectionModel a T
  ordinary : QuotientChange.extension a T ⋙
      (equivalence Λ' T).functor ≅
    (equivalence Λ T).functor ⋙ model.E
  derived : D a T ⋙ derivedFunctor Λ' T ≅
    derivedFunctor Λ T ⋙ model.T

/-- The scalar section comparisons are fixed on scalar-unit generators and by the
localization counits. In particular the quotient action is retained. -/
def ScalarSectionNormalized (T : Scheme.{u}) (c : ScalarSectionData a T) : Prop :=
  (∀ (M : Modules Λ T) (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W),
    (((c.ordinary.hom.app M) ≫ eqToHom (c.model.obj_eq _)).val.app W)
        (((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T)
          ((equivalence Λ T).functor.obj M)).presheaf).app W
            ((1 : (ring Λ' T).obj.obj W)
              ⊗ₜ[(ring Λ T).obj.obj W,
                ((sectionQuotient a T).hom.app W).hom] m)) ∧
  ∀ P : CochainComplex (Modules Λ T) ℤ,
    c.derived.hom.app (DerivedCategory.Q.obj P) ≫
        c.model.T.map (sectionLocalizationComparison Λ T P).hom ≫
        c.model.ε.app
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) =
      (derivedFunctor Λ' T).map (compute a T P) ≫
        (sectionLocalizationComparison Λ' T
          (((QuotientChange.extension a T).mapHomologicalComplex
            (.up ℤ)).obj P)).hom ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso c.ordinary (.up ℤ)).hom.app P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl ((equivalence Λ T).functor ⋙ c.model.E)) (.up ℤ)).inv.app P)

/-- The derived tensor bifunctor before scalar extension. -/
abbrev TensorIso (T : Scheme.{u}) :=
  Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙ D a T ≅
    ((D a T).prod (D a T)) ⋙ Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T)

set_option backward.isDefEq.respectTransparency false in
/-- The scalar regular unit in the derived monoidal category, using its actual
homotopy-localization unit and the ordinary multiplication unit. -/
def derivedScalarUnit (T : Scheme.{u}) :
    (D a T).obj (𝟙_ (DerivedCategory (Modules Λ T))) ⟶
      𝟙_ (DerivedCategory (Modules Λ' T)) :=
  letI := CondensedRing.internalScalarMonoidal a T
  letI := DerivedCategory.isIso_ε_Qh (Modules Λ' T)
  (D a T).map (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Modules Λ T))) ≫
    (scalarCounit a T).app (𝟙_ (HomotopyCategory (Modules Λ T) (.up ℤ))) ≫
    DerivedCategory.Qh.map
      (((QuotientChange.extension a T).mapHomotopyCategoryFactors (.up ℤ)).hom.app
          (𝟙_ (CochainComplex (Modules Λ T) ℤ)) ≫
        (HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex
            (QuotientChange.extension a T) (.up ℤ) 0).hom.app (𝟙_ _) ≫
            (HomologicalComplex.single _ (.up ℤ) 0).map
              (Functor.OplaxMonoidal.η (QuotientChange.extension a T)))) ≫
    inv (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Modules Λ' T)))

/-- The tensor comparison has the regular scalar unit and the tensor constraints. -/
def UnitCondition (T : Scheme.{u}) (b : TensorIso a T) : Prop :=
  IsIso (scalarRegularUnit a T) ∧ IsIso (derivedScalarUnit a T) ∧
    TensorConstraintCondition (D a T)
      (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T))
      (Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T))
      (𝟙_ (DerivedCategory (Modules Λ T))) (𝟙_ (DerivedCategory (Modules Λ' T)))
      (fun M N P ↦ α_ M N P) (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      (fun M N P ↦ α_ M N P) (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      b.hom (derivedScalarUnit a T)

/-- The actual sheafified scalar generator in the chosen ordinary section model.
The left-scalar convention s tensor m denotes m tensor s in the statement. -/
def sectionScalarElement (T : Scheme.{u}) (c : ScalarSectionData a T)
    (M : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
    (s : (ring Λ' T).obj.obj W) : (c.model.E.obj M).val.obj W :=
  (eqToHom (c.model.obj_eq M).symm).val.app W
    ((toSheafify (Scheme.ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T) M).presheaf).app W
        (s ⊗ₜ[(ring Λ T).obj.obj W, ((sectionQuotient a T).hom.app W).hom] m))

attribute [local irreducible] sectionScalarElement
  ModuleRingedComparison.qTensor

set_option backward.isDefEq.respectTransparency false in
/-- Section-side characterization of the canonical scalar tensor comparison.
The ordinary map is fixed on every sheafified pure scalar tensor. On every flat-term
K-flat pair its signed total, specified on each (i,j) summand, computes barB through
the model's own universal counit and the fixed section tensor localization maps. -/
def SectionTensorNormalized (T : Scheme.{u}) (c : ScalarSectionData a T)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T) : Prop :=
  ∃ e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
      (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
        (curriedTensor (modules Λ' T)),
    (∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W)
      (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
          (sectionScalarElement a T c (M ⊗ N) W (sectionPureTensor Λ T M N W m n) s) =
        sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
          (sectionScalarElement a T c M W m 1) (sectionScalarElement a T c N W n s)) ∧
    ∀ P Q : CochainComplex (modules Λ T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) Q →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (P.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (Q.X i)) →
      ∃ g : (c.model.E.mapHomologicalComplex (.up ℤ)).obj ((totalTensor Λ T).obj (P, Q)) ⟶
          (totalTensor Λ' T).obj
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q),
        (∀ (i j k : ℤ) (h : i + j = k),
          c.model.E.map
              (CochainComplex.ιMapBifunctor P Q (curriedTensor (modules Λ T)) i j k h) ≫
              g.f k =
            (e.app (P.X i)).app (Q.X j) ≫
              CochainComplex.ιMapBifunctor
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P)
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj Q)
                (curriedTensor (modules Λ' T)) i j k h) ∧
        barB.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            (tensor Λ' T).map (Prod.mkHom (c.model.ε.app P) (c.model.ε.app Q)) ≫
            (qTensor Λ' T).app
              ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
                (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q) =
          c.model.T.map ((qTensor Λ T).app (P, Q)) ≫
            c.model.ε.app ((totalTensor Λ T).obj (P, Q)) ≫ DerivedCategory.Q.map g

/-- The section image of the scalar tensorator, using the fixed tensor comparisons.
SectionTensorNormalized separately fixes its signed-total balancing normalization
on all section flat-term K-flat pairs. -/
def TensorSectionCondition (T : Scheme.{u}) (c : ScalarSectionData a T)
    (b : TensorIso a T)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T) : Prop :=
  ∀ M N : DerivedCategory (Modules Λ T),
    (derivedFunctor Λ' T).map (b.hom.app (M, N)) ≫
        (tensorComparison Λ' T).hom.app ((D a T).obj M, (D a T).obj N) =
      c.derived.hom.app (M ⊗ N) ≫
        c.model.T.map ((tensorComparison Λ T).hom.app (M, N)) ≫
        barB.hom.app ((derivedFunctor Λ T).obj M, (derivedFunctor Λ T).obj N) ≫
        (tensor Λ' T).map (Prod.mkHom (c.derived.inv.app M) (c.derived.inv.app N))

/-- The actual pullback tensor transformation and both adjunction structure maps
become the specified ringed operations under the fixed geometric comparisons. -/
def GeometricCondition
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules B T)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (∀ M N : DerivedCategory (internalModules B Y),
    HEq ((derivedFunctor B X).map
      (((CondensedRing.leftDerivedUpperStarTensor B f).app M).app N))
      ((derivedPullComparison B f).hom.app (M ⊗ N) ≫
        (derivedPullback B f).map ((tensorComparison B Y).hom.app (M, N)) ≫
        (tensorPullComparison B f).hom.app
          ((derivedFunctor B Y).obj M, (derivedFunctor B Y).obj N) ≫
        (tensor B X).map (Prod.mkHom
          ((derivedPullComparison B f).inv.app M) ((derivedPullComparison B f).inv.app N)) ≫
        (tensorComparison B X).inv.app
          ((internalDerivedPullback B f).obj M, (internalDerivedPullback B f).obj N))) ∧
  (∀ M : DerivedCategory (internalModules B Y),
    (derivedAdjunction B f).unit.app ((derivedFunctor B Y).obj M) =
      (derivedFunctor B Y).map ((normalizationInternalAdjunction B f).unit.app M) ≫
        (derivedPushComparison B f).hom.app ((internalDerivedPullback B f).obj M) ≫
        (derivedPushforward B f).map ((derivedPullComparison B f).hom.app M)) ∧
  (∀ N : DerivedCategory (internalModules B X),
    (derivedAdjunction B f).counit.app ((derivedFunctor B X).obj N) =
      (derivedPullback B f).map ((derivedPushComparison B f).inv.app N) ≫
        (derivedPullComparison B f).inv.app ((internalDerivedPushforward B f).obj N) ≫
        (derivedFunctor B X).map ((normalizationInternalAdjunction B f).counit.app N))

attribute [local semireducible] QuotientChange.L

/-- Section-side scalar/pullback normalization by the ordinary balancing comparison
and the actual section pullback localization maps and scalar-model counits.
The ordinary comparison is fixed through the ordinary section equivalences, independently
of lam or barLam: it carries f inverse (x tensor s) to f inverse x tensor f inverse s. -/
def SectionPullNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T) : Prop :=
  ∃ e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E,
    (∀ M : Modules Λ Y,
      (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
          cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          cX.model.E.map ((pullComparison Λ f).hom.app M) =
        (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
          (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
          e.hom.app ((equivalence Λ Y).functor.obj M)) ∧
    ∀ P : CochainComplex (modules Λ Y) ℤ,
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)

/-- Conjugation of the specified scalar/pullback comparison by the same scalar and
geometric realization maps. SectionPullNormalized separately fixes the ringed
comparison through the section pullback and scalar-model computation counits. -/
def PullSectionCondition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T) : Prop :=
  ∀ M : DerivedCategory (Modules Λ Y),
    (derivedFunctor Λ' X).map (lam.hom.app M) ≫
        cX.derived.hom.app ((L Λ f).obj M) ≫
        cX.model.T.map ((derivedPullComparison Λ f).hom.app M) =
      (derivedPullComparison Λ' f).hom.app ((D a Y).obj M) ≫
        (derivedPullback Λ' f).map (cY.derived.hom.app M) ≫
        barLam.hom.app ((derivedFunctor Λ Y).obj M)

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
