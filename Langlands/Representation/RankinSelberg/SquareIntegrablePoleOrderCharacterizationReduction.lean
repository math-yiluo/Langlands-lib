import Langlands.Representation.RankinSelberg.PairLFactorCharacterizationStatement
import Langlands.Representation.RankinSelberg.SquareIntegrableDataPoleOrder
import Langlands.Representation.RankinSelberg.SegmentLabelledDatumComparison
import Langlands.Representation.RankinSelberg.SupercuspidalProductGamma
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.Representation.Whittaker.SupercuspidalKirillovProof
import Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
import Langlands.Representation.Classification.SegmentHeadProductFiniteness

/-!
# Henniart's separation by pole orders, assuming the remaining prerequisites

Henniart 2002, Théorème 1.7(b): a non-supercuspidal irreducible representation
`π` of `GL_N(F)`, `N ≥ 2`, is determined by the orders of the poles at `s = 0`
of `L(s, π × ρ)` for the irreducible essentially square-integrable `ρ` of
`GL_r(F)`, `1 ≤ r ≤ N - 1`. This module derives
`SquareIntegrablePoleOrderCharacterizationStatement` from the prerequisites
that the Library states but does not yet prove: the square-integrable
Langlands exhaustion and classification (Henniart 2002, §2.8), JPSS 1983,
Theorem (9.5) in product form, Henniart 2002, §2.6, and JPSS 1983,
Proposition (8.1)(ii). The argument is Henniart's §4: the pole orders count
the segment links of the multisegment of `π`, and these counts determine the
multisegment.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial
open PadicField.TopologicalData

universe uF uV uW

/-- The prerequisites of Henniart 2002, Théorème 1.7(b), that the Library
states but does not prove: the square-integrable Langlands exhaustion and
classification of Henniart 2002, §2.8, for every `p`-adic field; JPSS 1983,
Theorem (9.5), in product form; Henniart 2002, §2.6; and JPSS 1983,
Proposition (8.1)(ii). -/
def SquareIntegrablePoleOrderCharacterizationPrerequisites : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    Classification.SquareIntegrableLanglandsExhaustion.{uF, uV} F F.canonicalTopologicalData ∧
      Classification.SquareIntegrableLanglandsClassification.{uF, uV} F
        F.canonicalTopologicalData) ∧
    SquareIntegrableDataLFactorStatement.{uF, uV, uW} ∧
    SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV} ∧
    SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV}

variable {p : ℕ} [Fact p.Prime]

/-- The multisegment of a segment labelling of a datum of `GL_n(F)` has
degree `n`. -/
theorem degree_map_univ_of_isSegmentLabelling {F : PadicField.{uF} p}
    {T : F.TopologicalData} {n : ℕ} {d : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n}
    {Δ : Fin d.shape.length → T.Segment.{max uF uV, uF}} (hΔ : IsSegmentLabelling d Δ) :
    Multisegment.degree (Finset.univ.val.map Δ : Multisegment.{max uF uV, uF} T) = n := by
  rw [Multisegment.degree, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact (Finset.sum_congr rfl fun i _ => (hΔ i).1).trans d.shape.sum_eq

/-- A segment head `σ` of `D`, moved to rank `m = deg D`, is equivalent to an
irreducible essentially square-integrable representation in any carrier
universe `max uF uW`. -/
theorem exists_isEssentiallySquareIntegrable_equiv_of_isSegmentHead
    {F : PadicField.{uF} p} {T : F.TopologicalData} (D : T.Segment.{max uF uV, uF})
    {m : ℕ} (hm : D.degree = m)
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear D.degree F.Carrier))
    (hσ : T.IsSegmentHead D σ) :
    letI := T.topology
    ∃ ρ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear m F.Carrier),
      Representation.IsIrreducible ρ.representation ∧
        T.IsEssentiallySquareIntegrable ρ.representation ∧
        Nonempty ((T.castRank hm σ).representation.Equiv ρ.representation) := by
  subst hm
  let := T.topology
  have hirr := hσ.isIrreducible
  have hesi : T.IsEssentiallySquareIntegrable σ.representation :=
    (Classification.segmentEssentialSquareIntegrableClassification.{uF, uV} F T _
      D.degree_pos σ hirr).mpr ⟨D, rfl, hσ⟩
  obtain ⟨ρ, hρ, ⟨e⟩⟩ :=
    padicIrreducibleSmoothSmallRealization.{uF, max uF uV, max uF uW} p F T D.degree σ hirr
  exact ⟨ρ, hρ, (T.isEssentiallySquareIntegrable_iff_of_equiv e).mp hesi, ⟨e⟩⟩

/-- **Henniart 2002, Théorème 1.7(b)**, assuming the square-integrable
Langlands exhaustion and classification, JPSS 1983, Theorem (9.5), Henniart
2002, §2.6, and JPSS 1983, Proposition (8.1)(ii). -/
theorem squareIntegrablePoleOrderCharacterization_of_classification
    (hE : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      Classification.SquareIntegrableLanglandsExhaustion.{uF, uV} F F.canonicalTopologicalData)
    (hC : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      Classification.SquareIntegrableLanglandsClassification.{uF, uV} F
        F.canonicalTopologicalData)
    (h95 : SquareIntegrableDataLFactorStatement.{uF, uV, uW})
    (hSH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (h81 : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV}) :
    SquareIntegrablePoleOrderCharacterizationStatement.{uF, uV, uW} := by
  intro p _ F ψ ν n π π' hπ _ hπ' _ hns htest
  let := F.canonicalTopologicalData.topology
  have h81i := supercuspidalUnequalRankLFactor.{uF, max uF uV, max uF uV}
  have hW : ∀ (r : ℕ) (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := r + 1)),
      IsOfWhittakerType r (standardCharacter ψ r) A.obj.representation := fun r A =>
    isOfWhittakerType_of_supercuspidalKirillov
      Langlands.supercuspidalKirillov.{uF, max uF uV} A.property.2 A.property.1
  obtain ⟨d, hd⟩ := hE p F (n + 2) (by omega) π hπ
  obtain ⟨d', hd'⟩ := hE p F (n + 2) (by omega) π' hπ'
  have hdq := hd.isLanglandsQuotient
  have hdq' := hd'.isLanglandsQuotient
  obtain ⟨Δ, hΔ⟩ := exists_isSegmentLabelling d
  obtain ⟨Δ', hΔ'⟩ := exists_isSegmentLabelling d'
  have heq : (Finset.univ.val.map Δ :
      Multisegment.{max uF uV, uF} F.canonicalTopologicalData) = Finset.univ.val.map Δ' := by
    apply multisegment_eq_of_poleLinkCount_eq (N := n + 2)
      (degree_map_univ_of_isSegmentLabelling hΔ) (degree_map_univ_of_isSegmentLabelling hΔ')
    · intro Γ hΓ h
      exact hns (isSupercuspidal_of_segmentLabelling_eq_singleton d π hdq Δ hΔ Γ hΓ h)
    · intro D hD
      obtain ⟨σ, hσ, -⟩ :=
        Classification.segmentSpecialConstituentExistence.{uF, max uF uV} F
          F.canonicalTopologicalData D.dual
      have hpos := D.degree_pos
      have ht : D.dual.degree = (D.degree - 1) + 1 := by
        rw [Segment.dual_degree]
        omega
      obtain ⟨ρ, hρ, hesi, hσρ⟩ :=
        exists_isEssentiallySquareIntegrable_equiv_of_isSegmentHead.{uF, uV, uW} D.dual ht σ hσ
      obtain ⟨P, P', hP, hP', hPP'⟩ := htest (D.degree - 1) (by omega) ρ hρ hesi
      rw [lPolynomialPoleOrderAtZero_eq_poleLinkCount ν h95 hSH h81 h81i hW π d hdq Δ hΔ
          ρ hρ hesi D.dual σ hσ ht hσρ hP,
        lPolynomialPoleOrderAtZero_eq_poleLinkCount ν h95 hSH h81 h81i hW π' d' hdq' Δ' hΔ'
          ρ hρ hesi D.dual σ hσ ht hσρ hP', Segment.dual_dual] at hPP'
      exact hPP'
  obtain ⟨e⟩ := nonempty_iso_of_segmentLabelling_eq (hC p F) (by omega) d d' π π' hdq hdq'
    Δ hΔ Δ' hΔ' heq
  exact ⟨SmoothRep.equivOfIso e⟩

/-- **Henniart 2002, Théorème 1.7(b)**, assuming
`SquareIntegrablePoleOrderCharacterizationPrerequisites`. -/
theorem squareIntegrablePoleOrderCharacterization_of_prerequisites
    (h : SquareIntegrablePoleOrderCharacterizationPrerequisites.{uF, uV, uW}) :
    SquareIntegrablePoleOrderCharacterizationStatement.{uF, uV, uW} :=
  squareIntegrablePoleOrderCharacterization_of_classification
    (fun p _ F => (h.1 p F).1) (fun p _ F => (h.1 p F).2) h.2.1 h.2.2.1 h.2.2.2

end Langlands.RankinSelberg
