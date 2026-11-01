import Langlands.HarmonicAnalysis.AdjacentRankUnipotentFourierStatement
import Langlands.HarmonicAnalysis.AdjacentRankFourierCancellation
import Langlands.HarmonicAnalysis.AdjacentRankSliceParameters
import Langlands.HarmonicAnalysis.AdjacentRankUnipotentMatrix
import Langlands.HarmonicAnalysis.AdjacentRankUnipotentIntegrability

/-! The rectangular unipotent Fourier identity of JPSS Section 6.2. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

open GeneralLinear RankinSelberg Whittaker

universe uK uF

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [T2Space K] [LocallyCompactSpace K]
  [TotallyDisconnectedSpace K]

private theorem adjacent_left_expansion
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (hself : IsSelfDual ψ ν) (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) K))
    (u : upperUnipotent (r + 1) K) :
    partialFourierEquiv ψ ν (r + 1) hself
      (rectangularTranslate (weylLong (r + 2) K * adjacentRankZeta K r) Φ)
        (rectangularJoin u.val.val (adjacentRankEpsilon K r)) *
          (inverseStandardCharacter ψ r u : ℂ) =
      ∫ y, ψ.complex (adjacentRankAntiTrace r (adjacentRankLeftMatrix r u y)) *
        rectangularFixedLastColumn
          ((weylLong (r + 1) K).val.mulVec (adjacentRankEpsilon K r)) Φ
          (adjacentRankLeftMatrix r u y) ∂rowMeasure ν (r + 1) := by
  rw [partialFourierEquiv_apply, partialFourierIntegral_join, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [rectangularTranslate_apply, ← adjacentRankLeftMatrix_join]
  simp only [rectangularFixedLastColumn_apply, adjacentRankAntiTrace,
    adjacentRankLeftMatrix_antiTrace, inverseStandardCharacter_apply]
  have heps : (∑ i, adjacentRankEpsilon K r i * y i) = y (Fin.last r) := by
    classical
    simp [adjacentRankEpsilon, Pi.single_apply, ite_mul]
  rw [heps]
  simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    unipotentFourierSum]
  ring

private theorem adjacent_right_expansion
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (hself : IsSelfDual ψ ν) (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) K))
    (u : upperUnipotent (r + 1) K) :
    rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
      (partialFourierEquiv ψ ν (r + 1) hself Φ)
        (rectangularJoin ((weylLong (r + 1) K).val * u.val.val)
          ((weylLong (r + 1) K).val.mulVec (adjacentRankEpsilon K r))) *
            (standardCharacter ψ r u : ℂ) =
      ψ.complex (adjacentRankShiftedAntiTrace r
          ((weylLong (r + 1) K).val * u.val.val)) *
        rectangularFourierIntegral ψ ν
          (rectangularFixedLastColumn
            ((weylLong (r + 1) K).val.mulVec (adjacentRankEpsilon K r)) Φ)
          ((weylLong (r + 1) K).val * u.val.val) := by
  rw [rectangularFourierEquiv_partial_fixedLastColumn,
    rectangularFourierEquiv_apply, standardCharacter_apply]
  simp only [adjacentRankShiftedAntiTrace, adjacentRank_weyl_shiftedAntiTrace,
    unipotentFourierSum]
  exact mul_comm _ _

variable [SecondCountableTopology K]

private theorem adjacent_unipotent_integral_eq
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (hself : IsSelfDual ψ ν) (r : ℕ)
    [MeasurableSpace (upperUnipotent (r + 1) K)]
    [BorelSpace (upperUnipotent (r + 1) K)]
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) K))
    (μ : Measure (upperUnipotent (r + 1) K)) [μ.IsHaarMeasure] :
    (∫ u : upperUnipotent (r + 1) K,
      partialFourierEquiv ψ ν (r + 1) hself
        (rectangularTranslate (weylLong (r + 2) K * adjacentRankZeta K r) Φ)
          (rectangularJoin u.val.val (adjacentRankEpsilon K r)) *
            (inverseStandardCharacter ψ r u : ℂ) ∂μ) =
    ∫ u : upperUnipotent (r + 1) K,
      rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
        (partialFourierEquiv ψ ν (r + 1) hself Φ)
          (rectangularJoin ((weylLong (r + 1) K).val * u.val.val)
            ((weylLong (r + 1) K).val.mulVec (adjacentRankEpsilon K r))) *
              (standardCharacter ψ r u : ℂ) ∂μ := by
  let e := upperEntryCoordinates (r + 1) (K := K)
  let b := (weylLong (r + 1) K).val.mulVec (adjacentRankEpsilon K r)
  let f := rectangularFixedLastColumn b Φ
  let fl := fun X => ψ.complex (adjacentRankAntiTrace r X) * f X
  let fr := fun Y => ψ.complex (adjacentRankShiftedAntiTrace r Y) *
    rectangularFourierIntegral ψ ν f Y
  let L : upperUnipotent (r + 1) K → ℂ := fun u =>
    partialFourierEquiv ψ ν (r + 1) hself
      (rectangularTranslate (weylLong (r + 2) K * adjacentRankZeta K r) Φ)
        (rectangularJoin u.val.val (adjacentRankEpsilon K r)) *
          (inverseStandardCharacter ψ r u : ℂ)
  let R : upperUnipotent (r + 1) K → ℂ := fun u =>
    rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
      (partialFourierEquiv ψ ν (r + 1) hself Φ)
        (rectangularJoin ((weylLong (r + 1) K).val * u.val.val) b) *
          (standardCharacter ψ r u : ℂ)
  obtain ⟨hr, hl, he⟩ := adjacentRankAffine_fourier_duality ψ ν hself r f
  have hpr := adjacentRankRightParam_preserving ν r
  have hpl := adjacentRankLeftParam_preserving ν r
  have hi := hpl.integrable_comp_of_integrable hl
  have hcols (X : UpperEntryPair (r + 1) → K) (y : Fin (r + 1) → K) :
      adjacentRankLeftParam r (X, y) = adjacentRankLeftMatrix r (e.symm X) y := by
    unfold adjacentRankLeftMatrix
    simpa only [e, Homeomorph.apply_symm_apply] using
      adjacentRankLeftParam_eq_columns r (e.symm X) y
  have hw (X : UpperEntryPair (r + 1) → K) :
      adjacentRankRightParam r X = (weylLong (r + 1) K).val * (e.symm X).val.val := by
    simpa only [e, Homeomorph.apply_symm_apply] using
      adjacentRankRightParam_eq_weyl r (e.symm X)
  have hL (X : UpperEntryPair (r + 1) → K) :
      L (e.symm X) = ∫ y, fl (adjacentRankLeftParam r (X, y))
        ∂rowMeasure ν (r + 1) := by
    simp only [hcols]
    exact adjacent_left_expansion ψ ν hself r Φ (e.symm X)
  have hR (X : UpperEntryPair (r + 1) → K) :
      R (e.symm X) = fr (adjacentRankRightParam r X) := by
    rw [hw]
    exact adjacent_right_expansion ψ ν hself r Φ (e.symm X)
  have pullback {A B : Type uK} [MeasurableSpace A] [MeasurableSpace B]
      {μa : Measure A} {μb : Measure B} {p : A → B}
      (hp : MeasurePreserving p μa μb) {g : B → ℂ} (hg : Integrable g μb) :
      (∫ x, g (p x) ∂μa) = ∫ y, g y ∂μb := by
    have hm : AEStronglyMeasurable g (μa.map p) :=
      hp.map_eq.symm ▸ hg.aestronglyMeasurable
    exact (integral_map hp.measurable.aemeasurable hm).symm.trans (by rw [hp.map_eq])
  have hcoord : (∫ X, L (e.symm X) ∂upperEntryProductMeasure ν (r + 1)) =
      ∫ X, R (e.symm X) ∂upperEntryProductMeasure ν (r + 1) := by
    calc
      _ = ∫ X, ∫ y, fl (adjacentRankLeftParam r (X, y)) ∂rowMeasure ν (r + 1)
          ∂upperEntryProductMeasure ν (r + 1) := by
            apply integral_congr_ae
            filter_upwards [] with X using hL X
      _ = ∫ z, fl (adjacentRankLeftParam r z)
          ∂(upperEntryProductMeasure ν (r + 1)).prod (rowMeasure ν (r + 1)) :=
            (integral_prod _ hi).symm
      _ = ∫ X, fr (adjacentRankRightParam r X) ∂upperEntryProductMeasure ν (r + 1) :=
            (pullback hpl hl).trans (he.symm.trans (pullback hpr hr).symm)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with X using (hR X).symm
  obtain ⟨c, _, hc⟩ := exists_upperEntry_integral ν μ
  change (∫ u, L u ∂μ) = ∫ u, R u ∂μ
  rw [hc L, hc R]
  exact congrArg (fun t : ℂ => (c : ℂ) * t) hcoord

/-- The closed rectangular unipotent Fourier identity, with both convergence
assertions and the prescribed common group Haar. -/
theorem adjacentRankUnipotentFourier : AdjacentRankUnipotentFourierStatement.{uF} := by
  intro p hp F
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  haveI : BorelSpace F.Carrier := ⟨rfl⟩
  haveI : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  haveI : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro ψ ν hself r
  letI : MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
  haveI : BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
  intro Φ
  haveI : SecondCountableTopology F.Carrier :=
    F.canonicalTopologicalData.secondCountableTopology
  haveI : SigmaFinite ν.measure := selfDualSigmaFinite F.Carrier ψ ν hself
  obtain ⟨hL, hR⟩ := adjacentRankUnipotent_integrable ψ ν hself r Φ
    (unipotentHaar F.Carrier r)
  exact ⟨hL, hR, adjacent_unipotent_integral_eq ψ ν hself r Φ
    (unipotentHaar F.Carrier r)⟩

end Langlands.HarmonicAnalysis
