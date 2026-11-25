/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Over
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
public import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
public import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
public import Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Precoverage.Generates
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Basic.Finite.Prod
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
public import WeilConjectures.Topology.Stratification
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationFlat
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import all WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Karoubian
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.AlgebraicGeometry.Open.OpenClosedFlatness
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import all WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Point.Over
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Flat models and generators

Source: Weil conjectures blueprint, main-20261015, `sec-six-functors-basics/`
`lemma-flat-models-generators`, statement and complement (blueprint: lemma-flat-models-generators).

## Main statements

* `proEtaleFlatModel`: bounded flat constructible representatives.
* `proEtaleFlatStratification`: finite projective constant local models on strata.
* `proEtaleThickGeneration`, `boundedConstructible_induction`: the Noetherian complement.
* `proEtaleThickGeneration_eq`: equality with the thick envelope in the standing setting.

The generator predicates below spell out the statement's locally closed extension by zero.
They use the scheme-theoretic image of the actual stratum immersion, not an arbitrary closed
subscheme with the same underlying set. Closed direct image is exact here, so its value on
`L[0]` also represents `Rg_*j_!L`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

-- Request the shared locally-bijective instance at the coefficient universe used here.
attribute [local instance] WeilConjectures.sfAbBijective

/-- The etale closure generators `Rg_*j_!L`: the closed direct image is exact, so the
ordinary sheaf in degree zero is its derived value. The equation on `j` fixes the open
factor through the scheme-theoretic image of the stratum immersion. Lisse flat sheaves
have finite projective constant local models over the finite coefficient ring.
Source: blueprint `lemma-flat-models-generators`, complement
(blueprint: lemma-flat-models-generators). -/
def etaleClosureGenerators (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    ObjectProperty (Etale.DerivedCategoryModule A X) :=
  fun K ↦ ∃ (str : Stratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j)
    (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} A)),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    IsFiniteLocallyConstantSheaf L ∧ ObjectProperty.flat L ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} A) (str.immersion i).imageι).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj L)))

/-- The Noetherian complement on the etale site, with the recorded finite-value
constructibility and the recorded Tor tests on every module sheaf in degree zero.
Source: blueprint `lemma-flat-models-generators`, complement
(blueprint: lemma-flat-models-generators).

Proof (node steps 1 and 3--7): use lem-sf-etale-flat-constructible directly, without
comparison descent. Clauses 1--2 of lemma-flat-models-generators--2 give an ordered
stratification and a finite extension filtration of each flat constructible term.
Finite stalks give finite generation on each locally constant restriction, and inverse
image preserves flatness. The canonical open factor through the scheme-theoretic image
therefore identifies each filtration factor with an etaleClosureGenerators object.
The short exact sequences give distinguished single-object triangles, so finite
induction proves the property for each term, starting with the zero filtration member.
Apply HomotopyCategory.mem_subcategory_of_strictly_bounded to the inverse image of P
under Qh; this implements the bounded stupid-tail induction. Finally transport across
the quotient-comparison and representing isomorphisms. -/
theorem boundedConstructible_induction
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (P : ObjectProperty (Etale.DerivedCategoryModule A X))
    [P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]
    (hP : etaleClosureGenerators X A ≤ P)
    (K : Etale.DerivedCategoryModule A X)
    (hbc : Etale.DerivedCategory.isBoundedConstructible A X K)
    (hTor : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b K) :
    P K := by
  obtain ⟨a, b, hab, ht⟩ := hTor
  obtain ⟨Pc, hf, hc, hz, ⟨e⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel A X a b hab K hbc).1 ht
  have hterm (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (hFc : IsConstructibleEtaleModuleSheaf F) (hFf : ObjectProperty.flat F) :
      P ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
    obtain ⟨str, ho, hp⟩ := etale_flatConstructible_orderedStratification X A F hFc hFf
    obtain ⟨M, hM0, ⟨eM⟩, hM⟩ :=
      (etale_flatConstructible_extensionFiltration X A F str ho hp).1
    have hG (k : Fin str.n) :
        P ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
            ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F))) := by
      let L := (Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F
      have hL : IsFiniteLocallyConstantSheaf L := by
        have : IsLocallyConstantSheaf L := (hp k).1
        refine { isFinitelyGenerated_sheafFiber := ?_ }
        intro Ω _ _ x
        have := ((hp k).2 Ω x).1
        rw [ModuleCat.isFinitelyGenerated_iff]
        exact Module.Finite.of_finite
      have hLf : ObjectProperty.flat L :=
        Functor.PreservesFlat.flat_obj (F := Etale.upperStar _ (str.immersion k)) hFf
      have : TopologicalSpace.NoetherianSpace (str.domain k) :=
        (str.immersion k).isEmbedding.isInducing.noetherianSpace
      apply hP
      exact ⟨str, k, (str.immersion k).toImage, inferInstance, L,
        Scheme.Hom.toImage_imageι _, hL, hLf, ⟨Iso.refl _⟩⟩
    have hm : ∀ k : Fin (str.n + 1),
        P ((_root_.DerivedCategory.singleFunctor _ 0).obj (M k)) := by
      intro k
      induction k using Fin.induction with
      | zero =>
        exact P.prop_of_isZero (Functor.map_isZero _ hM0)
      | succ k ih =>
        obtain ⟨f, g, h, hs⟩ := hM k
        exact P.ext_of_isTriangulatedClosed₂ _ hs.singleTriangle_distinguished ih (hG k)
    exact P.prop_of_iso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso eM)
      (hm (Fin.last str.n))
  have : Pc.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ hz q (.inl hq)
  have : Pc.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ hz q (.inr hq)
  have hPc := HomotopyCategory.mem_subcategory_of_strictly_bounded
    (P.inverseImage _root_.DerivedCategory.Qh) Pc a b
    (fun n _ _ ↦ hterm (Pc.X n) (hc n) (hf n))
  exact P.prop_of_iso e (P.prop_of_iso
    ((_root_.DerivedCategory.quotientCompQhIso _).app Pc) hPc)

end AlgebraicGeometry
