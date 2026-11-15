import Langlands.Geometry.Building.Kottwitz.ReductiveFunctorialityReduction
import Langlands.Geometry.Building.Kottwitz.ReductiveMapRemainingInputs
import Langlands.Geometry.Building.Kottwitz.CentralTorusExactnessProof
import Langlands.Geometry.Building.Kottwitz.FundamentalInertiaMapProof
import Langlands.Geometry.Building.Kottwitz.TorusInertiaComparisonProof
import Langlands.Geometry.Building.Kottwitz.TorusMapProof
import Langlands.Geometry.Building.Kottwitz.TorusNormNaturality
import Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupMapNaturality
import Langlands.GroupScheme.ZExtensionMorphismDominationProof
import Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityProof

/-! # Functoriality and torus compatibility of the reductive Kottwitz map -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

/-- KP Lemma 11.5.1 functoriality and torus compatibility, from reductive Kottwitz existence.
Every other input is a published proof. -/
theorem reductiveKottwitzFunctoriality_of_existence
    (hexist : ReductiveKottwitzExistenceStatement.{u}) :
    ReductiveKottwitzFunctorialityStatement.{u} :=
  have hmap : FundamentalInertiaMapStatement.{u} := fundamentalInertiaMapStatement
  reductiveKottwitzFunctoriality_of_inputs algebraicFundamentalGroupComparison
    (algebraicFundamentalGroupMap_of_comparison algebraicFundamentalGroupComparison)
    hmap torusInertiaComparison_proof
    (simplyConnectedDerivedKottwitz_of_norm_inputs algebraicFundamentalGroupComparison
      (algebraicFundamentalGroupMap_of_comparison algebraicFundamentalGroupComparison)
      torusFundamentalComparison_proof hmap torusInertiaComparison_proof torusKottwitzExistence)
    hexist zExtensionMorphismDomination
    (fun F _ _ _ _ k _ _ _ _ _ _ _ _ hS hT f x =>
      torusKottwitz_natural_of_existence F k hS hT f torusKottwitzExistence x)

/-- **Functoriality and torus compatibility of the reductive Kottwitz map**
(Kaletha–Prasad, Lemma 11.5.1). The selected reductive Kottwitz homomorphism is natural for
every morphism of connected reductive groups, and on a torus it agrees with the
norm-and-valuation torus Kottwitz map under the canonical inertia comparison. -/
theorem reductiveKottwitzFunctoriality :
    ReductiveKottwitzFunctorialityStatement.{u} := by
  have hcommon : ZExtensionCommonDominationStatement.{u} := by
    intro k _ G hG z t
    obtain ⟨w, r, s, hr, hs⟩ := zExtensionMorphismDomination k G G hG hG z t (𝟙 G)
    exact ⟨w, r, s, hr, by simpa using hs⟩
  exact reductiveKottwitzFunctoriality_of_existence
    (reductiveKottwitzExistence_of_remaining_inputs fundamentalInertiaMapStatement
      (zExtensionPointSurjectivity_of_inducedTorusQuotient inducedTorusQuotientPointSurjectivity)
      centralTorusInertiaExactness hcommon)

end Langlands.Geometry.Building.Kottwitz
