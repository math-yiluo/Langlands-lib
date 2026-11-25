/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-! # Canonical scalar and chart comparisons between etale and pro-etale sites

Source: Stacks Project, proetale.tex, Tag 0GLZ; sites-cohomology.tex,
Tags 06YY, 0D6D and 07A4; the Charts paragraph of lemma-sp-reduction--2
(blueprint: lem-sp-etale-chart-comparison-isos).

The inverse images below are the ordinary derived inverse images. Tensor and
shift comparisons are the existing normalized derived comparisons. Finite roots
and their scalar extensions use the recorded same-unit root comparison.
-/

@[expose] public noncomputable section

set_option Elab.async true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorCompNatIso
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryNatIso
  CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.singleFunctorCompLeftDerivedFunctorIso
  CategoryTheory.Functor.leftDerivedFunctorCompIso
  CategoryTheory.Functor.leftDerivedFunctorNatIso

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
  CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]

private instance sheafSmallColimits (J : GrothendieckTopology C)
    (R : Type (u + 1)) [CommRing R] :
    HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
  ⟨fun _ ↦ Sheaf.instHasColimitsOfShape⟩

/-- Sheafified balanced extension of constant scalars, with the new ring acting on
its tensor factor. Source: Stacks, Tags 03EK and 06YY
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def fixedCoefficientScalarExtension (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J (ModuleCat.{u + 1} B) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f)

/-- Additivity follows from the actual scalar-extension/restriction adjunction.
Source: Stacks, Tag 06YY (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance fixedCoefficientScalarExtension_additive (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    (fixedCoefficientScalarExtension J f).Additive :=
  (Sheaf.adjunction J
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)).left_adjoint_additive

private theorem fixedExtension_preservesKFlat (J : GrothendieckTopology C)
    {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (fixedCoefficientScalarExtension J φ).PreservesKFlatQuasiIso := by
  classical
  let E := fixedCoefficientScalarExtension J φ
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have : E.Additive := adj.left_adjoint_additive
  have : PreservesLimitsOfSize.{0, 0} U := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits U := inferInstance
  have : PreservesColimitsOfSize.{0, 0} U :=
    (Sheaf.restrictCoextendScalarsAdj J φ).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits U := inferInstance
  let _ := φ.toAlgebra
  let X := (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R S)
  let e : E ⋙ U ≅ tensorRight X := Sheaf.extendScalarsCompRestrictScalarsIso J R S
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa X
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  infer_instance

/-- Everywhere-defined ordinary derived scalar extension. Source: Stacks, Tags
06YS, 06YT and 06YY (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: resolve by flat-term K-flat complexes (06YS). Restricted back to A,
ordinary extension is tensoring with the constant A-module B. The cone of a
quasi-isomorphism between K-flat complexes is acyclic K-flat, and remains
acyclic after this tensor (06YT). Therefore extension descends along these
resolutions. The resolving-class construction gives the pointwise universal
left-derived pair (06YY), with its counit computing ordinary extension on
K-flat representatives. No flatness of B over A is used. -/
@[instance]
theorem fixedCoefficientScalarExtension_hasPointwiseLeftDerivedFunctor
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    ((fixedCoefficientScalarExtension J f).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
        (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)) := by
  let E := fixedCoefficientScalarExtension J f
  let U := Sheaf.restrictScalars J f
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)
  have : PreservesLimitsOfSize.{0, 0} U := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits U := inferInstance
  have : PreservesColimitsOfSize.{0, 0} U :=
    (Sheaf.restrictCoextendScalarsAdj J f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits U := inferInstance
  have : E.PreservesKFlatQuasiIso := fixedExtension_preservesKFlat J f
  exact (Adjunction.exists_leftDerived_adjunction E U adj
    (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat
    (fun K ↦ by
      obtain ⟨r⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
        (Φ := (HomologicalComplex.quasiIso
          (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).localizerMorphismKFlat) K
      exact ⟨r.X₁.obj, r.w, r.X₁.property,
        (HomologicalComplex.mem_quasiIso_iff _).1 r.hw⟩)
    (fun g hK hL hg ↦ by
      let _ := hg
      exact E.quasiIso_mapHomologicalComplex_map_of_kFlat hK hL g)).1

attribute [local irreducible] fixedCoefficientScalarExtension

/-- The canonical total left derived extension, the universal right Kan extension
of ordinary extension followed by localization. Its universal property determines
it up to the unique comparison preserving its counit.
Source: Stacks, Tag 06YY (blueprint: lem-sp-etale-chart-comparison-isos). -/
def fixedCoefficientDerivedExtension (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) :=
  ((fixedCoefficientScalarExtension J f).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q).totalLeftDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ))

/-- The universal counit of the displayed ordinary left derived extension.
Source: Stacks, Tag 06YY (blueprint: lem-sp-etale-chart-comparison-isos). -/
def fixedCoefficientDerivedExtensionCounit (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    DerivedCategory.Q ⋙ fixedCoefficientDerivedExtension J f ⟶
      (fixedCoefficientScalarExtension J f).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  ((fixedCoefficientScalarExtension J f).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q).totalLeftDerivedCounit DerivedCategory.Q
      (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ))

attribute [local irreducible] fixedCoefficientDerivedExtension
  fixedCoefficientDerivedExtensionCounit

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.EtaleChartComparison

/-- Ordinary etale coefficient modules. Source: Stacks, Tag 05RU
(blueprint: lem-sp-etale-chart-comparison-isos). -/
abbrev Et (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) : Type (u + 2) :=
  Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)

/-- Ordinary pro-etale coefficient modules. Source: Stacks, Tags 099R and 05RU
(blueprint: lem-sp-etale-chart-comparison-isos). -/
abbrev Pro (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) : Type (u + 2) :=
  Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)

/-- Cache the right adjoint underlying etale sheafification.
Source: Stacks, 00WX (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etWeakSheafify (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} R) := HasSheafify.isRightAdjoint

/-- Cache the right adjoint underlying pro-etale sheafification.
Source: Stacks, 00WX (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proWeakSheafify (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R) :=
  HasSheafify.isRightAdjoint

/-- Existing small colimits, made explicit for the unbounded derived construction.
Source: Stacks, Tag 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etSmallColimits (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Et R T) := ⟨fun _ ↦ Sheaf.instHasColimitsOfShape⟩

/-- Cache the existing Abelian structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etAbelian (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    Abelian (Et R T) := inferInstance

/-- Cache the existing Abelian structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proAbelian (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    Abelian (Pro R T) := inferInstance

/-- Cache the existing MonoidalPreadditive structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etMonoidalPreadditive (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    MonoidalPreadditive (Et R T) := inferInstance

/-- Cache the existing MonoidalPreadditive structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proMonoidalPreadditive (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    MonoidalPreadditive (Pro R T) := inferInstance

/-- Cache the existing SymmetricCategory structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etSymmetricCategory (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    SymmetricCategory (Et R T) := inferInstance

/-- Cache the existing MonoidalClosed structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etMonoidalClosed (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    MonoidalClosed (Et R T) := inferInstance

/-- Cache the existing MonoidalClosed structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proMonoidalClosed (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    MonoidalClosed (Pro R T) := inferInstance

/-- Cache the existing functorial flat resolution structure.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etHasFunctorialFlatResolution (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    CategoryTheory.Abelian.HasFunctorialFlatResolution (Et R T) := inferInstance

/-- Cache the existing functorial flat resolution structure.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proHasFunctorialFlatResolution (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    CategoryTheory.Abelian.HasFunctorialFlatResolution (Pro R T) := inferInstance

/-- The exact comparison, localized at quasi-isomorphisms. Source: Stacks, 0GLZ
(blueprint: lem-sp-etale-chart-comparison-isos). -/
abbrev nu (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    DerivedCategory (Et R T) ⥤ DerivedCategory (Pro R T) :=
  (comparisonUpperStar (ModuleCat.{u + 1} R) T).leftDerivedFunctor

/-- Scheme inverse image on ordinary pro-etale complexes. Source: Stacks, Tag 0D6D
(blueprint: lem-sp-etale-chart-comparison-isos). -/
abbrev proPull (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    DerivedCategory (Pro R T) ⥤ DerivedCategory (Pro R T') :=
  (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v).leftDerivedFunctor

/-- The exact comparison on degree-zero sheaves. Source: Stacks 05RU.
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def nuSingle (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    DerivedCategory.singleFunctor (Et R T) 0 ⋙ nu R T ≅
      comparisonUpperStar (ModuleCat.{u + 1} R) T ⋙
        DerivedCategory.singleFunctor (Pro R T) 0 :=
  Functor.singleFunctorCompLeftDerivedFunctorIso
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)

attribute [local irreducible] nuSingle

/-- Ordinary balanced scalar comparison, fixed by the commuting restriction square.
Both right adjoints restrict the same sections with the same A-action. Consequently
left-adjoint uniqueness gives the ordinary balanced-tensor map, in B-modules.
Source: Stacks, Tags 03EL and 06YY (blueprint: lem-sp-etale-chart-comparison-isos). -/
def scalarSheafIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    fixedCoefficientScalarExtension T.smallEtaleTopology f ⋙
        comparisonUpperStar (ModuleCat.{u + 1} B) T ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        fixedCoefficientScalarExtension (Scheme.ProEt.topology T) f :=
  ((Sheaf.adjunction T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)).comp
      (comparisonAdjunction (ModuleCat.{u + 1} B) T)).leftAdjointUniq
    ((comparisonAdjunction (ModuleCat.{u + 1} A) T).comp
      (Sheaf.adjunction (Scheme.ProEt.topology T)
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)))

attribute [local irreducible] scalarSheafIso



/-- The normalized finite-root scalar comparison already specified by its generators.
The theorem determines its map uniquely: each local root goes to the same unit and
its scalar factor is unchanged. Source: Stacks, Tags 0GLZ and 03EL
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def rootIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).obj
        (Scheme.finiteEtaleTateLine T N R hR) ≅
      Scheme.finiteRootProTensor R N hN hR T :=
  Classical.choose (Scheme.finiteRootSiteComparison R) N hN hR T hT

/-- Nonnegative powers of the actual pro-etale root tensor, with constant unit in degree zero.
Source: Stacks, Section 03PK and Tag 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def proTwist (R : Type (u + 1)) [CommRing R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u}) : ℕ → Pro R T
  | 0 => 𝟙_ _
  | 1 => Scheme.finiteRootProTensor R N hN hR T
  | c + 2 => proTwist R N hN hR T (c + 1) ⊗ Scheme.finiteRootProTensor R N hN hR T

/-- Iterated canonical tensor comparison, initialized by the unit and the same-unit root map.
Source: Stacks, Tags 03EL, 0GLZ and 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def twistSheafIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) : ∀ c : ℕ,
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).obj
        (Scheme.finiteEtaleTateTwist T N R hR c) ≅ proTwist R N hN hR T c
  | 0 => (Functor.Monoidal.εIso (comparisonUpperStar (ModuleCat.{u + 1} R) T)).symm
  | 1 => rootIso R N hN hR T hT
  | c + 2 =>
    (Functor.Monoidal.μIso (comparisonUpperStar (ModuleCat.{u + 1} R) T)
      (Scheme.finiteEtaleTateTwist T N R hR (c + 1))
      (Scheme.finiteEtaleTateLine T N R hR)).symm ≪≫
    (twistSheafIso R N hN hR T hT (c + 1) ⊗ᵢ rootIso R N hN hR T hT)

attribute [local irreducible] twistSheafIso rootIso

/-- The degree-zero finite-root comparison in the ordinary derived categories.
Source: Stacks, Tags 0GLZ and 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def twistLineIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (c : ℕ) :
    (nu R T).obj ((DerivedCategory.singleFunctor (Et R T) 0).obj
        (Scheme.finiteEtaleTateTwist T N R hR c)) ≅
      (DerivedCategory.singleFunctor (Pro R T) 0).obj (proTwist R N hN hR T c) :=
  (nuSingle R T).app (Scheme.finiteEtaleTateTwist T N R hR c) ≪≫
    (DerivedCategory.singleFunctor (Pro R T) 0).mapIso (twistSheafIso R N hN hR T hT c)

attribute [local irreducible] twistLineIso

/-- The canonical derived tensor comparison for the site inverse image.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def nuTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :
    (nu R T).obj (K ⊗ M) ⟶ (nu R T).obj K ⊗ (nu R T).obj M :=
  ((Functor.leftDerivedTensorComparison
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)).app K).app M

/-- The same canonical tensor arrow with its source and target written explicitly.
The transports are identities on the displayed bifunctor objects.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def nuTensor (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :
    (nu R T).obj (K ⊗ M) ⟶ (nu R T).obj K ⊗ (nu R T).obj M :=
  nuTensorRaw R T K M

/-- The specified tensor comparison is invertible.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: use flat-term K-flat resolutions in both variables. Comparison inverse
image is exact and preserves flat objects; its canonical ordinary tensor map is
an isomorphism. Localization gives the inverse of nuTensor, independently of
resolutions, as in Functor.isIso_leftDerivedTensorComparison. -/
@[instance]
theorem nuTensor_isIso (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) : IsIso (nuTensor R T K M) := by
  unfold nuTensor nuTensorRaw
  dsimp only [nu]
  infer_instance

attribute [local irreducible] nuTensor nuTensorRaw

/-- The specified derived twist comparison: the derived tensor comparison followed by
one tensor the finite-root comparison, including the constant-unit case c=0.
Source: Stacks, Tag 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def twistIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (c : ℕ) (L : DerivedCategory (Et R T)) :
    (nu R T).obj (L ⊗ (DerivedCategory.singleFunctor (Et R T) 0).obj
      (Scheme.finiteEtaleTateTwist T N R hR c)) ≅
    (nu R T).obj L ⊗ (DerivedCategory.singleFunctor (Pro R T) 0).obj
      (proTwist R N hN hR T c) :=
  asIso (nuTensor R T L ((DerivedCategory.singleFunctor (Et R T) 0).obj
    (Scheme.finiteEtaleTateTwist T N R hR c))) ≪≫
  (Iso.refl ((nu R T).obj L) ⊗ᵢ twistLineIso R N hN hR T hT c)

attribute [local irreducible] twistIso

/-- The canonical shift map, obtained from termwise inverse image with the signed
cochain differential. Source: Stacks, Tag 05RU
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def shiftIso (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) (s : ℤ) :
    shiftFunctor (DerivedCategory (Et R T)) s ⋙ nu R T ≅
      nu R T ⋙ shiftFunctor (DerivedCategory (Pro R T)) s :=
  Functor.isoWhiskerLeft (shiftFunctor (DerivedCategory (Et R T)) s)
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.commShiftIso s ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).leftDerivedFunctorIsoMapDerivedCategory.symm
      (shiftFunctor (DerivedCategory (Pro R T)) s)




/-- The localization comparison for the exact site inverse image, on cochain complexes.
Source: Stacks, Tags 0GLZ and 05RU (blueprint: lem-sp-etale-chart-comparison-isos). -/
def nuQFactor (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ nu R T ≅
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategoryFactors

attribute [local irreducible] nuQFactor

/-- The equation specifying the scalar comparison on every flat-term K-flat model.
The ordinary arrow is scalarSheafIso, so this retains its B-action and tensor normalization.
Source: Stacks, Tags 06YY and 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def ScalarModel {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u})
    (alpha : fixedCoefficientDerivedExtension T.smallEtaleTopology f ⋙ nu B T ⟶
      nu A T ⋙ fixedCoefficientDerivedExtension (Scheme.ProEt.topology T) f) : Prop :=
  ∀ P : CochainComplex (Et A T) ℤ,
    (HomologicalComplex.quasiIso (Et A T) (.up ℤ)).kFlat P →
    (∀ i : ℤ, exactFunctor _ _ (tensorRight (P.X i))) →
    IsIso ((fixedCoefficientDerivedExtensionCounit T.smallEtaleTopology f).app P) ∧
    IsIso ((fixedCoefficientDerivedExtensionCounit (Scheme.ProEt.topology T) f).app
      (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    alpha.app (DerivedCategory.Q.obj P) ≫
        (fixedCoefficientDerivedExtension (Scheme.ProEt.topology T) f).map
          ((nuQFactor A T).hom.app P) ≫
        (fixedCoefficientDerivedExtensionCounit (Scheme.ProEt.topology T) f).app
          (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex (.up ℤ)).obj P) =
      (nu B T).map
          ((fixedCoefficientDerivedExtensionCounit T.smallEtaleTopology f).app P) ≫
        (nuQFactor B T).hom.app
          (((fixedCoefficientScalarExtension T.smallEtaleTopology f).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (scalarSheafIso f T) (.up ℤ)).hom.app P)

attribute [local irreducible] ScalarModel




end AlgebraicGeometry.ProEtale.EtaleChartComparison
