import Langlands.Representation.Classification.ConjugateMultisegmentSocle
import Langlands.Representation.Aubert.SegmentPolynomialSurjectivity

/-!
# Hermitian symmetry of the multisegment of a unitarizable representation

Tadić 1986, §2.1–2.4: if `π = ⟨a⟩` is irreducible and unitarizable, then `a^+ = a`. An
invariant positive form identifies the complex conjugate `π̄` with the smooth dual `π̃`, so
`π̃` is labelled both by `ā` (conjugating every segment) and by `ã` (dualizing every
segment). Labels determine their multisegment, so `ā = ã`; for a unitary cuspidal `ρ` this
matches `[ν^x ρ, ν^(x+l-1) ρ]` with `[ν^(-(x+l-1)) ρ, ν^(-x) ρ]`.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData
open Aubert Aubert.SegmentPolynomialSurjectivity

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

namespace UnitarizableSocleHermitianSymmetryProof

/-- A Zelevinsky socle `A` of a multisegment `b` gives the label `[A]` of `b`. -/
theorem isLabel_of_isZelevinskySocle {N : ℕ} {b : T.Multisegment.{max uF uV, uF}}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : b.IsZelevinskySocle A) :
    letI := T.topology
    ∃ hA : A.IsIrreducible, IsLabel F T b N (irreducibleIsoClass N F.Carrier A hA) := by
  let := T.topology
  obtain ⟨d, hd, hs⟩ := h
  have hA : A.IsIrreducible := hs.2.2.1
  exact ⟨hA, A, hA, rfl, d, hd, hs.isZelevinskySubrepresentation⟩

/-- A label determines its multisegment (Zelevinsky's triangularity, in the published
rank-order form). -/
theorem eq_of_isLabel {a b : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (ha : IsLabel F T a m c) (hb : IsLabel F T b m c) : a = b := by
  let hx := binaryProductExactness.{uF, uV} F T
  let hl := gradedInductionRingLaws F T hx
  let ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology :=
    Classical.choice (HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T)
  have hstep := highestDerivativeLabelStep F T ψ
  exact Multisegment.RankLE.antisymm
    (rankLE_of_coeff_zeta_pos F T hx hl ψ hstep m c a b ha
      (lt_of_lt_of_le one_pos (one_le_coeff_zeta_of_isLabel F T hx hl hb)))
    (rankLE_of_coeff_zeta_pos F T hx hl ψ hstep m c b a hb
      (lt_of_lt_of_le one_pos (one_le_coeff_zeta_of_isLabel F T hx hl ha)))

variable {F T}

/-- For a unitary cuspidal `ρ`, the dual of `[ν^x ρ, ν^(x+l-1) ρ]` is the conjugate of
`[ν^(-(x+l-1)) ρ, ν^(-x) ρ]`. -/
theorem dual_eq_conj {ρ : T.CuspidalDatum.{max uF uV, uF}} (hρ : ρ.IsUnitary) (x : ℝ) {l : ℕ}
    (hl : 0 < l) :
    (⟨ρ.twist x, l, hl⟩ : T.Segment.{max uF uV, uF}).dual =
      (⟨ρ.twist (-(x + ((l : ℝ) - 1))), l, hl⟩ : T.Segment.{max uF uV, uF}).conj := by
  change (Segment.mk (CuspidalProductContragredient.dualDatum
      ((ρ.twist x).twist ((l - 1 : ℕ) : ℝ))) l hl : T.Segment.{max uF uV, uF}) =
    Segment.mk (ρ.twist (-(x + ((l : ℝ) - 1)))).conj l hl
  rw [CuspidalDatum.twist_twist, CuspidalProductContragredient.dualDatum_twist,
    CuspidalDatum.conj_twist, ← CuspidalDatum.conj_eq_dualDatum hρ, Nat.cast_sub hl,
    Nat.cast_one]
  congr 3
  ring

end UnitarizableSocleHermitianSymmetryProof

open scoped Classical in
open UnitarizableSocleHermitianSymmetryProof in
/-- Tadić 1986, §2.1–2.4: the multisegment of an irreducible unitarizable representation
is Hermitian, `a^+ = a`. -/
theorem unitarizableSocleHermitianSymmetry :
    UnitarizableSocleHermitianSymmetry.{uF, uV} F T := by
  intro N π a hirr hu ha ρ hρ x l hl
  let := T.topology
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨d, hd, -⟩ := ha
    have h0 : a = 0 := eq_zero_of_degree_eq_zero F T (hd ▸ degree_multisegment F T d)
    simp [h0]
  let := T.generalLinearTopologicalGroup N
  have hadm : IsAdmissible π.representation :=
    (CuspidalSupport.cuspidalEmbedding F T N π hirr).1
  obtain ⟨b⟩ := hu
  have h1 : Multisegment.IsZelevinskySocle (a.map Segment.conj) π.contragredient :=
    Multisegment.IsZelevinskySocle.conj
      (b.smoothDualEquiv (GeneralLinear.compactOpen_cofinal F T N) hadm)
      (fun g v => b.toSmoothDual_apply_action hadm.1 g v) ha
  have h2 : Multisegment.IsZelevinskySocle (a.map Segment.dual) π.contragredient :=
    Multisegment.IsZelevinskySocle.contragredient hN ha
  obtain ⟨_, hl1⟩ := isLabel_of_isZelevinskySocle F T h1
  obtain ⟨_, hl2⟩ := isLabel_of_isZelevinskySocle F T h2
  have heq : a.map Segment.conj = a.map Segment.dual := eq_of_isLabel F T hl1 hl2
  have hdual : Function.Injective (Segment.dual : T.Segment.{max uF uV, uF} → _) :=
    Function.LeftInverse.injective Segment.dual_dual
  rw [← Multiset.count_map_eq_count' _ a hdual, ← heq, dual_eq_conj hρ x hl,
    Multiset.count_map_eq_count' _ a Segment.conj_injective]

end Langlands.Classification
