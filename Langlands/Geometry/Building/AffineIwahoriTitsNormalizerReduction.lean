import Langlands.Geometry.Building.AffineIwahoriTitsInputStatements
import Langlands.Geometry.Building.IwahoriWeylNormalizerAffineWeylReduction
import Langlands.Geometry.Building.ChamberParahoricNormalizerProof
import Langlands.Geometry.Building.ChamberParahoricGenerationProof
import Langlands.Geometry.Building.AffineRankOneTwoCellProof
import Langlands.Geometry.Building.ChamberSimpleFactorizationProof
import Langlands.Geometry.Building.RootGroupParahoricFiltrationProof
import Langlands.Geometry.Building.ChamberConjugateIntersectionProof
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylAssembly
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylReduction
import Langlands.Geometry.Building.SimplyConnectedFacetFixingReduction
import Langlands.Geometry.Building.FacetFixingWeylReduction
import Langlands.Geometry.Building.ValuationAffineRootSystems
import Langlands.Geometry.Building.AffineChamberTransitivity
import Langlands.GroupScheme.Derived.CentralSplitTorusProductProof
import Langlands.GroupScheme.SimplyConnected.KneserTitsCentralizerReduction
import Langlands.GroupScheme.SimplyConnected.KneserTitsFactorReduction
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleRationalGenerationProof
import Langlands.GroupScheme.SimplyConnected.AnisotropicFactorCentralizerProof
import Langlands.GroupScheme.Reductive.NormalIsogenyComplementProof
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.SimplyConnected.LocalRankOneClassificationReduction
import Langlands.GroupScheme.SimplyConnected.RankOneLeviFactorExistenceProof
import Langlands.GroupScheme.SimplyConnected.RankOneLeviDerivedGenerationProof
import Langlands.GroupScheme.SimplyConnected.RankOneLeviCocenterGenerationProof
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleWeilRestrictionProof
import Langlands.GroupScheme.Rational.AffineWeilSplitRankProof
import Langlands.GroupScheme.Rational.AffineWeilParabolicElementaryProof
import Langlands.GroupScheme.Quaternionic.LocalSymplecticKneserTitsProof

/-!
# The apartment-only affine Iwahori–Tits statement and the affine Weyl image of `N^♮`

Given the proved Library inputs, `AffineIwahoriTitsStatement` is equivalent to
`SimplyConnectedNormalizerAffineWeylStatement`, the range part of Kaletha–Prasad,
Theorem 7.5.3(2). The forward implication composes
`iwahoriWeylNormalizerAffineWeylReduction` with
`affineIwahoriTitsStatement_of_inputStatements` and the six proved input statements. The
converse uses the action comparison of an affine Iwahori–Tits system for one actual chamber,
together with `G(F)^♮ ≤ G(F)^0` and the proved rank-one factorization.

Further down, the target is reduced along the published route through facet fixing and the
Kneser–Tits statements to three open local arithmetic statements.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The apartment-only affine Iwahori–Tits statement follows from the range part of
KP Theorem 7.5.3(2): the exact sequence comes from `iwahoriWeylNormalizerAffineWeylReduction`
and the six remaining inputs of `affineIwahoriTitsStatement_of_inputStatements` are proved. -/
theorem affineIwahoriTitsStatement_of_simplyConnectedNormalizerAffineWeyl
    (hW : SimplyConnectedNormalizerAffineWeylStatement.{u}) :
    AffineIwahoriTitsStatement.{u} :=
  affineIwahoriTitsStatement_of_inputStatements (iwahoriWeylNormalizerAffineWeylReduction hW).1
    chamberParahoricNormalizer chamberParahoricGeneration affineRankOneTwoCell
    chamberSimpleFactorization rootGroupParahoricFiltration chamberConjugateIntersection

/-- Conversely, the apartment-only affine Iwahori–Tits statement implies the range part of
KP Theorem 7.5.3(2). For one actual chamber, the action comparison of the Iwahori–Tits system
places the apartment action of every element of `N(F) ∩ G(F)^0`, hence of
`N(F) ∩ G(F)^♮`, in `W(Ψ)`; the reverse inclusion is the proved rank-one realization of the
affine reflections. -/
theorem simplyConnectedNormalizerAffineWeyl_of_affineIwahoriTits
    (h : AffineIwahoriTitsStatement.{u}) :
    SimplyConnectedNormalizerAffineWeylStatement.{u} := by
  intro F _ _ _ _ G _ P hA
  refine le_antisymm ?_
    (affineWeylGroup_le_simplyConnectedNormalizer_map_of_rankOneStatement
      rootRankOneFactorization F G P hA)
  let C := AffineRootSystem.baseChamber
    P.toValuationBuildingData.isAffineRootSystemWithRankZero_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨hN, hZ, e, he⟩ := h F G P hA C.val C.property
  rintro _ ⟨n, hn, rfl⟩
  have hn0 : n ∈ P.normalizerZeroComponent :=
    P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hn
  rw [← he.action_compatible ⟨n, hn0⟩]
  exact (e (P.affinePartMk ⟨n, hn0⟩)).property

/-- The apartment-only affine Iwahori–Tits statement (the `G(F)^0` branch of KP
Theorem 7.5.3(1),(2)) is equivalent to the range part of KP Theorem 7.5.3(2):
`N(F) ∩ G(F)^♮` acts on the apartment through exactly `W(Ψ)`. -/
def AffineIwahoriTitsNormalizerAffineWeylEquivalenceStatement : Prop :=
  AffineIwahoriTitsStatement.{u} ↔ SimplyConnectedNormalizerAffineWeylStatement.{u}

/-- Given the proved Library inputs, the apartment-only affine Iwahori–Tits statement is
equivalent to the range part of KP Theorem 7.5.3(2). -/
theorem affineIwahoriTitsStatement_iff_simplyConnectedNormalizerAffineWeyl :
    AffineIwahoriTitsNormalizerAffineWeylEquivalenceStatement.{u} :=
  ⟨simplyConnectedNormalizerAffineWeyl_of_affineIwahoriTits,
    affineIwahoriTitsStatement_of_simplyConnectedNormalizerAffineWeyl⟩

/-- The target from pointwise fixing of facets by their normalizer stabilizers for simply
connected groups; the split-torus product input is proved. -/
theorem affineIwahoriTitsStatement_of_simplyConnectedFacetFixing
    (hfix : SimplyConnectedFacetFixingStatement.{u}) :
    AffineIwahoriTitsStatement.{u} :=
  affineIwahoriTitsStatement_of_simplyConnectedNormalizerAffineWeyl
    (simplyConnectedNormalizerAffineWeylReduction hfix derivedCentralSplitTorusProduct)

/-- The target from Kneser–Tits for split-torus centralizers in simply connected groups. -/
theorem affineIwahoriTitsStatement_of_simplyConnectedKneserTitsCentralizer
    (hKT : SimplyConnectedKneserTitsCentralizerStatement.{u}) :
    AffineIwahoriTitsStatement.{u} :=
  affineIwahoriTitsStatement_of_simplyConnectedFacetFixing
    (simplyConnectedFacetFixing_of_kneserTitsCentralizer hKT)

/-- The target from local Kneser–Tits for isotropic almost-simple simply connected groups;
all structural inputs of the factor reduction are proved. -/
theorem affineIwahoriTitsStatement_of_localKneserTits
    (hKT : LocalKneserTitsStatement.{u}) :
    AffineIwahoriTitsStatement.{u} :=
  affineIwahoriTitsStatement_of_simplyConnectedKneserTitsCentralizer
    (simplyConnectedKneserTitsCentralizer_of_factors simplyConnectedAlmostSimpleRationalGeneration
      (simplyConnectedKneserTitsFactor_of_localKT_and_structural_inputs hKT
        semisimpleNormalIsogenyComplement rationalBruhat rootRankOneFactorization
        parabolicDynamic smoothMaximalSplitTorusConjugacy)
      simplyConnectedAnisotropicFactorCentralizer)

/-- The target from the three open local arithmetic inputs of the published Kneser–Tits
route: vanishing of `H¹` for simply connected groups over nonarchimedean local fields, the
classification of absolutely almost-simple simply connected groups of split rank one, and
Kneser–Tits for the quaternionic spin groups. -/
theorem affineIwahoriTitsStatement_of_localArithmeticInputs
    (hloc : LocalSimplyConnectedCocycleVanishingStatement.{u})
    (hcl : LocalRankOneClassificationStatement.{u})
    (hspin : Quaternionic.LocalSpinKneserTitsStatement.{u}) :
    AffineIwahoriTitsStatement.{u} :=
  affineIwahoriTitsStatement_of_localKneserTits
    (localKneserTits_of_rankOneLeviFactors_of_classification
      ⟨rankOneLeviFactorExistence, rankOneLeviDerivedGeneration, rankOneLeviCocenterGeneration⟩
      hloc simplyConnectedAlmostSimpleWeilRestriction affineWeilSplitRank
      affineWeilParabolicElementarySubgroup
      ⟨hcl, Quaternionic.localSymplecticKneserTits, hspin⟩)

end Langlands.Geometry.Building
