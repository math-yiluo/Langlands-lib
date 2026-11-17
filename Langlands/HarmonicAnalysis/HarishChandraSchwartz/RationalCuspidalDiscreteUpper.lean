import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzCentralDiscreteUpper
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralSubgroupQuotientHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralStatements

/-! # The actual rational cuspidal upper inclusion under local estimates -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The local actual VIII.4.2 upper step. Its inputs are central and ambient
weight estimates and finite projected cuspidal level spans for the displayed
group and choices. No positive form or coefficient decomposition is supplied. -/
def RationalCuspidalDiscreteUpperEstimateStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s)
      (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
      (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure],
      CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ) →
      L2Weights muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ) →
      letI := (rationalPoints.map s).range.normal_of_le_center
        hs.isCentralSplitTorus.isCentral.range_le_center
      letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
      ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
        (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
        (∀ J : OpenSubgroup (rationalPoints G), IsCompact (J : Set (rationalPoints G)) →
          FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ J.toSubgroup)) →
        rationalCuspidalCentralImage hKc hPK ρ muA χ ⊆
          (discreteSeriesCentralCoefficientSpace.{u, max u uV}
            (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
            mu χ : Set (rationalPoints G → ℂ))

/-- All representation and coefficient inputs of the rational upper step are
constructed from the displayed local estimates. -/
theorem rationalCuspidalDiscreteUpperEstimate :
    RationalCuspidalDiscreteUpperEstimateStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i _ ν _ K hKc hPK N _ ρ _ T s hs muA _ muG _ hw hL
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  have : BorelSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := ⟨rfl⟩
  intro mu _ χ _ hu hfinite
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  let : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  let : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
  have : muG.Regular := inferInstance
  have : muG.IsMulRightInvariant := Haar.isMulRightInvariant_of_modularCharacter_eq_one
    (RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter) muG
  have : muA.IsMulRightInvariant := by
    constructor
    intro a
    have he :
        (fun x : (rationalPoints.map s).range => x * a) = (fun x => a * x) := by
      funext x
      exact Subtype.ext (Subgroup.mem_center_iff.mp
        (hs.isCentralSplitTorus.isCentral.range_le_center a.property) x)
    rw [he, map_mul_left_eq_self]
  have : mu.IsInvInvariant := (rationalSplitCentralQuotientHaar_invariant hG s hs mu).2
  have hstable : IsTranslationStable (rationalTranslationWeights K.isOpen hKc hPK ρ)
      (rationalCuspidalSubmodule hKc hPK ρ) := by
    intro g₁ g₂ f hf I hI muU hmuU
    exact (hf I hI muU hmuU).translate g₁ g₂
  apply schwartzCentralIntegralImage_subset_discreteSeries_of_weights
    (isClosed_range_splitComponent G s hs)
    hs.isCentralSplitTorus.isCentral.range_le_center muA muG mu
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalCuspidalSubmodule hKc hPK ρ) hstable hw hL χ hu
  · exact fun J => CompactOpenSubgroup.cofinal J
  · exact hfinite

end Langlands.HarishChandraSchwartz
