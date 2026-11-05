import Langlands.Representation.Classification.MinimalIntegralCuspidalRunsSegmentInductionProof
import Langlands.Representation.Classification.IntegralSegmentHeadScalarNormProof
import Langlands.Representation.Classification.SegmentConstituentRealTwistCompatibilityProof
import Langlands.Representation.Classification.OrderedIntegralSegmentInductionSquareIntegrableCollapseProof
import Langlands.Representation.Classification.ConsecutiveIntegralCuspidalWordSegmentHeadStatement
import Langlands.Representation.Classification.ConsecutiveIntegralCuspidalWordSegmentHeadProof
import Langlands.Representation.Classification.SquareIntegrableIntegralCuspidalJacquetWordStatement
import Langlands.Representation.Classification.SquareIntegrableIntegralCuspidalJacquetWordProof
import Langlands.Representation.Classification.SegmentSquareIntegrabilityStatement
import Langlands.Representation.Classification.SegmentSpecialEssentialSquareIntegrabilityProof
import Langlands.Representation.Classification.SegmentConstituentCompatibilityStatement
import Langlands.Representation.Classification.IntegralCuspidalJacquetWordOrderedRunsProof
import Langlands.Representation.Classification.AdjacentCuspidalJacquetInterchangeProof
import Langlands.Representation.Classification.RepeatedCuspidalTripleJacquetTransferProof
import Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Classification.TwoSegmentHeadCommutationProof

/-!
# The segment classification of essentially square-integrable representations

An analytic square-integrable representation has an actual integral cuspidal
Jacquet word. The proved local word moves give ordered minimal consecutive
runs. Run extraction, the common scalar-norm formula and the strict analytic
cone force one run, giving the strong segment head. Real determinant twists
then give the essentially square-integrable assertion. The reverse direction
uses the proved analytic construction for every special segment quotient.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The extraction, scalar and cone interfaces reduce ordered minimal runs to
one consecutive word, whose supplied detection interface gives the strong head. -/
private theorem segmentHead_of_squareIntegrable_of_minimalRuns
    (hruns : MinimalIntegralCuspidalRunsSegmentInduction.{uF,uV} F T)
    (hscalar : IntegralSegmentHeadScalarNorm.{uF,uV} F T)
    (hcollapse : OrderedIntegralSegmentInductionSquareIntegrableCollapse.{uF,uV} F T)
    (hconsecutive : ConsecutiveIntegralCuspidalWordSegmentHead.{uF,uV} F T)
    (hcommute : TwoSegmentHeadCommutation.{uF,uV} F T) :
    letI := T.topology
    ∀ (m : ℕ) (_hm : 0 < m) (n : ℕ), 0 < n →
      ∀ (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
        (r : ℕ) (a : Fin r → ℤ) (l : Fin r → ℕ) (_hl : ∀ i, 0 < l i)
        (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
        π.IsIrreducible → T.IsSquareIntegrable π.representation →
        IntegralCuspidalJacquetWord F T m n A π
          (List.ofFn (fun i => List.ofFn (fun j : Fin (l i) =>
            a i - (j.val : ℤ)))).flatten →
        (∀ v : List ℤ, IntegralCuspidalJacquetWord F T m n A π v →
          v.Perm (List.ofFn (fun i => List.ofFn (fun j : Fin (l i) =>
            a i - (j.val : ℤ)))).flatten →
          ¬ List.Lex (· < ·) v (List.ofFn (fun i =>
            List.ofFn (fun j : Fin (l i) => a i - (j.val : ℤ)))).flatten) →
        Monotone a →
        ∃ (Δ : Segment.{max uF uV,uF} T) (h : Δ.degree = n),
          T.IsSegmentHead Δ (h.symm ▸ π) := by
  let := T.topology
  intro m hm n hn A r a l hl π hπi hπsq hword hmin hmono
  classical
  have hπa : π.IsAdmissible := hπsq.isAdmissible
  have hπf : π.HasFiniteLength := SmoothRep.hasFiniteLength_of_isIrreducible hπi
  let : π.representation.IsIrreducible := hπi
  let : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      π.representation.asModule
  let Δ : Fin r → Segment.{max uF uV,uF} T := fun i =>
    ⟨⟨m, hm, T.supercuspidalClassRealPowerTwist m
      ((a i - ((l i - 1 : ℕ) : ℤ) : ℤ) : ℝ) A.isoClass⟩, l i, hl i⟩
  obtain ⟨hsum, X, hXi, hXa, hhead, hquot, hemb⟩ :=
    hruns m hm n hn A r a l hl π hπi hπa hπf hword hmin
  let d : SegmentProductDatum.{max uF uV,uF} T n :=
    ⟨r, Δ, hsum, X⟩
  let ρ : CuspidalDatum.{max uF uV,uF} T := ⟨m, hm, A.isoClass⟩
  let b : Fin r → ℤ := fun i => a i - ((l i - 1 : ℕ) : ℤ)
  have hcoord (i : Fin r) : (Δ i).HasIntegralCoordinates ρ (b i) (a i) := by
    refine ⟨rfl, ?_⟩
    have := hl i
    dsimp only [Δ, b]
    omega
  obtain ⟨t, ht⟩ := hscalar ρ
  choose c hc hnorm using fun i =>
    ht (Δ i) (b i) (a i) (hcoord i) (X i) (hhead i)
  have hr : r = 1 :=
    hcollapse hcommute n hn π hπsq d hhead hemb ρ a b hcoord hmono t c hc hnorm
  subst r
  have hw : IntegralCuspidalJacquetWord F T m n A π
      (List.ofFn (fun j : Fin (l 0) => a 0 - (j.val : ℤ))) := by
    simpa only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
      List.flatten_nil, List.append_nil] using hword
  have hrank : l 0 * m = n := by
    simpa only [Fin.sum_univ_one] using hsum
  cases hrank
  exact ⟨Δ 0, rfl, hconsecutive m hm A (l 0) (hl 0) (a 0) π hπi hπa hw⟩

/-- The proved local word moves select ordered minimal runs in the original
permutation class; the supplied run-to-head interfaces then apply. -/
private theorem segmentHead_of_squareIntegrable_of_integralWord
    (hruns : MinimalIntegralCuspidalRunsSegmentInduction.{uF,uV} F T)
    (hscalar : IntegralSegmentHeadScalarNorm.{uF,uV} F T)
    (hcollapse : OrderedIntegralSegmentInductionSquareIntegrableCollapse.{uF,uV} F T)
    (hconsecutive : ConsecutiveIntegralCuspidalWordSegmentHead.{uF,uV} F T)
    (hcommute : TwoSegmentHeadCommutation.{uF,uV} F T) :
    letI := T.topology
    ∀ (m : ℕ) (_hm : 0 < m) (n : ℕ), 0 < n →
      ∀ (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
        (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
        π.IsIrreducible → T.IsSquareIntegrable π.representation →
        ∀ w₀ : List ℤ, IntegralCuspidalJacquetWord F T m n A π w₀ →
        ∃ (Δ : Segment.{max uF uV,uF} T) (h : Δ.degree = n),
          T.IsSegmentHead Δ (h.symm ▸ π) := by
  let := T.topology
  intro m hm n hn A π hπi hπsq w₀ hword
  classical
  have hπa : π.IsAdmissible := hπsq.isAdmissible
  have hπf : π.HasFiniteLength := SmoothRep.hasFiniteLength_of_isIrreducible hπi
  obtain ⟨w, hw, hperm, hmin, runs, hpos, hchain, hflat⟩ :=
    integralCuspidalJacquetWordOrderedRuns F T
      (adjacentCuspidalJacquetInterchange F T)
      (twoSupercuspidalNonadjacentProductIrreducible F T)
      (repeatedCuspidalTripleJacquetTransfer F T)
      m n A π hπi hπa hπf w₀ hword
  let a : Fin runs.length → ℤ := fun i => (runs.get i).1
  let l : Fin runs.length → ℕ := fun i => (runs.get i).2
  have hl : ∀ i, 0 < l i := fun i => hpos _ (List.get_mem runs i)
  have htopchain : (runs.map Prod.fst).IsChain (· ≤ ·) :=
    (List.isChain_map Prod.fst).mpr hchain
  have htop : List.ofFn a = runs.map Prod.fst := by
    simpa only [a, List.get_eq_getElem] using
      List.ofFn_getElem_eq_map runs Prod.fst
  have hmono : Monotone a := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact List.pairwise_ofFn.mp (htop ▸ htopchain.pairwise) hij
  have hrun (s : ℤ × ℕ) :
      (List.range s.2).map (fun j => s.1 - (j : ℤ)) =
        List.ofFn (fun j : Fin s.2 => s.1 - (j.val : ℤ)) := by
    change ((List.range s.2).flatMap (fun j : ℕ => [(j : ℤ)])).map
      (fun j : ℤ => s.1 - j) = _
    rw [← List.map_eq_flatMap, List.map_map]
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  have htuple :
      List.ofFn (fun i => List.ofFn (fun j : Fin (l i) =>
        a i - (j.val : ℤ))) =
        runs.map (fun s => List.ofFn (fun j : Fin s.2 =>
          s.1 - (j.val : ℤ))) := by
    simpa only [a, l, List.get_eq_getElem] using
      List.ofFn_getElem_eq_map runs
        (fun s => List.ofFn (fun j : Fin s.2 => s.1 - (j.val : ℤ)))
  have heq : w = (List.ofFn (fun i => List.ofFn (fun j : Fin (l i) =>
      a i - (j.val : ℤ)))).flatten := by
    rw [hflat, htuple, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro s _
    exact hrun s
  apply segmentHead_of_squareIntegrable_of_minimalRuns F T
    hruns hscalar hcollapse hconsecutive hcommute
    m hm n hn A runs.length a l hl π hπi hπsq (heq ▸ hw) ?_ hmono
  intro v hv hvperm
  rw [← heq]
  apply hmin v hv
  exact (hvperm.trans (List.Perm.of_eq heq.symm)).trans hperm

/-- An irreducible positive-rank smooth representation is analytically
essentially square-integrable exactly when it is the strong special head of
some segment of that rank. -/
theorem segmentEssentialSquareIntegrableClassification :
    SegmentEssentialSquareIntegrableClassification.{uF,uV} F T := by
  let := T.topology
  intro n hn π hπi
  constructor
  · rintro ⟨s, hs⟩
    let π₀ := π.twist (T.determinantPowerCharacter n (-s))
      (T.isOpen_ker_determinantPowerCharacter n (-s))
    have hπ₀i : π₀.IsIrreducible :=
      (SmoothRep.isIrreducible_twist_iff _ _ π).mpr hπi
    have hπ₀sq : T.IsSquareIntegrable π₀.representation := hs
    obtain ⟨m, hm, A, w, _, hw⟩ :=
      squareIntegrableIntegralCuspidalJacquetWordExistence F T n hn π₀ hπ₀i hπ₀sq
    obtain ⟨Δ, he, hΔ⟩ :=
      segmentHead_of_squareIntegrable_of_integralWord F T
        (minimalIntegralCuspidalRunsSegmentInduction F T)
        (integralSegmentHeadScalarNorm F T)
        (orderedIntegralSegmentInductionSquareIntegrableCollapse F T)
        (consecutiveIntegralCuspidalWordSegmentHead F T)
        (twoSegmentHeadCommutation F T) m hm n hn A π₀ hπ₀i hπ₀sq w hw
    cases he
    refine ⟨Δ.twist s, rfl, ?_⟩
    apply ((segmentConstituentRealTwistCompatibility.{uF,max uF uV} F T
      (Δ.twist s) (-s) π).2.1).mpr
    change T.IsSegmentHead ((Δ.twist s).twist (-s)) π₀
    have hcancel : (Δ.twist s).twist (-s) = Δ := by
      rw [Segment.twist_twist, neg_add_cancel, Segment.twist_zero]
    convert hΔ using 1
    rfl
  · rintro ⟨Δ, he, hΔ⟩
    cases he
    exact segmentSpecialEssentialSquareIntegrability F T Δ π hΔ.isSegmentQuotient

end Langlands.Classification
