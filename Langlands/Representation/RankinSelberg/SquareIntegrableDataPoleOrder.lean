import Langlands.Representation.RankinSelberg.SegmentPairPoleOrder
import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.Classification.LanglandsDatumRealization
import Langlands.Representation.Classification.SquareIntegrableUnitarityProof
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Induction.SingleBlock
import Langlands.Group.GL.OneBlockShape
import Langlands.Representation.Twist.SubquotientProof

/-!
# Pole orders at `s = 0` through essentially square-integrable data

Let `π` be an irreducible quotient of `i(π_1, …, π_r)` for essentially
square-integrable `π_i = St(Δ_i)`, and `ρ ≃ St(D)` irreducible essentially
square-integrable. Assuming JPSS 1983, Theorem (9.5) in product form, Henniart
2002, §2.6, JPSS 1983, Proposition (8.1), and the Whittaker type of irreducible
supercuspidal representations, `L(s, π × ρ)` has a pole of order
`#{i : SegmentPoleLink Δ_i D^∨}` at `s = 0`, the count `poleLinkCount` of the
multisegment `{Δ_1, …, Δ_r}` at `D^∨`.
-/

noncomputable section

namespace Langlands

universe uF uV uW

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- An irreducible essentially square-integrable representation `ρ` of `GL_n(F)`,
`n > 0`, has a real exponent `α` for which `ν^(-α) ρ` carries an invariant positive
definite form. -/
theorem nonempty_unitaryExponentData {n : ℕ} (hn : 0 < n) {V : Type uV}
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    (hρ : Representation.IsIrreducible ρ)
    (hesi : letI := T.topology; T.IsEssentiallySquareIntegrable ρ) :
    Nonempty (UnitaryExponentData (T.determinantNorm n) ρ) := by
  let := T.topology
  obtain ⟨s, hs⟩ := hesi
  obtain ⟨form⟩ := glSquareIntegrableUnitarity.{uF, uV} p F T n hn V _
    ((isIrreducible_twist_iff _ _).mpr hρ) hs
  exact ⟨⟨s, form⟩⟩

namespace SquareIntegrableLanglandsDatum

variable {T}

/-- The essentially square-integrable Langlands datum of `GL_n(F)`, `n > 0`, with the
single block `ρ`, for `ρ` irreducible and essentially square-integrable. Its
exponent is a chosen one. -/
def single {n : ℕ} (hn : 0 < n)
    (ρ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hρ : letI := T.topology; Representation.IsIrreducible ρ.representation)
    (hesi : letI := T.topology; T.IsEssentiallySquareIntegrable ρ.representation) :
    SquareIntegrableLanglandsDatum.{uV, uF} T n where
  shape := CuspidalSupport.LeviAdmissibility.oneBlock n hn
  blocks _ := ρ
  irreducible _ := hρ
  essentiallySquareIntegrable _ := hesi
  unitaryExponent _ := (T.nonempty_unitaryExponentData hn hρ hesi).some
  antitone _ _ _ := le_rfl

/-- The single-block datum of `ρ` presents every representation equivalent to `ρ`. -/
theorem single_isLanglandsQuotient {n : ℕ} (hn : 0 < n)
    (ρ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hρ : letI := T.topology; Representation.IsIrreducible ρ.representation)
    (hesi : letI := T.topology; T.IsEssentiallySquareIntegrable ρ.representation)
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (e : letI := T.topology; ρ.representation.Equiv π.representation) :
    (single hn ρ hρ hesi).IsLanglandsQuotient π := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let B := CuspidalSupport.LeviAdmissibility.oneBlock n hn
  let E := T.singleBlockNormalizedProductEquiv B rfl (fun _ => ρ.representation)
    (fun _ => ρ.isSmooth) ⟨0, Nat.one_pos⟩
  let E' := (E.trans (T.castRankEquiv rfl ρ)).trans e
  exact ⟨(isIrreducible_iff_of_equiv e).mp hρ, E'.toIntertwiningMap, E'.surjective⟩

/-- A datum with blocks in `max uF uV` presenting `π` has an equivalent realization
with blocks in `uV` presenting `π`. -/
theorem exists_withBlocks_isLanglandsQuotient {n : ℕ}
    (d : SquareIntegrableLanglandsDatum.{max uF uV, uF} T n)
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hd : d.IsLanglandsQuotient π) :
    letI := T.topology
    ∃ (b : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (d.shape.size i) F.Carrier))
      (E : ∀ i, (d.blocks i).representation.Equiv (b i).representation),
      (d.withBlocks b E).IsLanglandsQuotient π := by
  let := T.topology
  choose b _ E using fun i => padicIrreducibleSmoothSmallRealization.{uF, max uF uV, uV}
    p F T (d.shape.size i) (d.blocks i) (d.irreducible i)
  exact ⟨b, fun i => (E i).some,
    Classification.IsIrreducibleQuotient.of_equiv (d.withBlocksInducedEquiv b _) hd⟩

end SquareIntegrableLanglandsDatum

end PadicField.TopologicalData

namespace RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial
open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime]

section Count

variable {F : PadicField.{uF} p} {T : F.TopologicalData}

open Classical in
/-- The link count of the multisegment of a finite family of segments. -/
theorem poleLinkCount_map_univ {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T)
    (D : Segment.{uV, uF} T) :
    poleLinkCount (Finset.univ.val.map Δ) D =
      ∑ i, if SegmentPoleLink (Δ i) D then 1 else 0 := by
  rw [poleLinkCount, Multiset.countP_map, ← Finset.card_filter]
  rfl

end Count

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

open Classical in
/-- `lPolynomialPoleOrderAtZero_of_segmentHeads` for representations of `GL_n(F)` and
`GL_t(F)` with `n = deg Δ` and `t = deg Δ'`, carried to the segment ranks by
the rank equalities. -/
theorem lPolynomialPoleOrderAtZero_of_segmentHeads_cast
    (hSH : SegmentHeadLFactorStatement.{uF, uV, uV})
    (h81 : SupercuspidalEqualRankLFactorStatement.{uF, uV, uV})
    (h81i : SupercuspidalUnequalRankLFactorStatement.{uF, uV, uV})
    (hW : ∀ (r : ℕ) (A : letI := F.canonicalTopologicalData.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1)),
      letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType r (standardCharacter ψ r) A.obj.representation)
    {n t : ℕ} (Δ Δ' : F.canonicalTopologicalData.Segment.{uV, uF})
    (hn : Δ.degree = n) (ht : Δ'.degree = t)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear n F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ'.degree F.Carrier))
    (hπ : F.canonicalTopologicalData.IsSegmentHead Δ (hn.symm ▸ π))
    (hσ : F.canonicalTopologicalData.IsSegmentHead Δ' σ) {P : ℂ[X]}
    (hP : letI := F.canonicalTopologicalData.topology
      IsPadicRankLPolynomial F ψ ν.val π.representation
        (F.canonicalTopologicalData.castRank ht σ).representation P) :
    lPolynomialPoleOrderAtZero P = if SegmentPoleLink Δ Δ'.dual then 1 else 0 := by
  subst hn ht
  exact lPolynomialPoleOrderAtZero_of_segmentHeads ν hSH h81 h81i hW Δ Δ' π σ hπ hσ hP

/-- **Pole order at `s = 0` through essentially square-integrable data.** Let `π` be
an irreducible quotient of `i(π_1, …, π_r)` for an essentially square-integrable
datum `d` of `GL_(n+1)(F)` whose blocks are the segment heads `π_i = St(Δ_i)`, and
let `ρ` be an irreducible essentially square-integrable representation of
`GL_(t+1)(F)` equivalent to a head `σ = St(D)`. Assuming JPSS 1983, Theorem (9.5)
in product form, Henniart 2002, §2.6, JPSS 1983, Proposition (8.1), and the
Whittaker type of irreducible supercuspidal representations, every L-polynomial
`P` of `π × ρ` has a root of multiplicity `poleLinkCount {Δ_1, …, Δ_r} D^∨` at
`1`: `L(s, π × ρ)` has a pole of that order at `s = 0`. -/
theorem lPolynomialPoleOrderAtZero_eq_poleLinkCount
    (h95 : SquareIntegrableDataLFactorStatement.{uF, uV, uW})
    (hSH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (h81 : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (h81i : SupercuspidalUnequalRankLFactorStatement.{uF, max uF uV, max uF uV})
    (hW : ∀ (r : ℕ) (A : letI := F.canonicalTopologicalData.topology
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := r + 1)),
      letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType r (standardCharacter ψ r) A.obj.representation)
    {n t : ℕ}
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (d : SquareIntegrableLanglandsDatum.{max uF uV, uF} F.canonicalTopologicalData (n + 1))
    (hd : d.IsLanglandsQuotient π)
    (Δ : Fin d.shape.length → F.canonicalTopologicalData.Segment.{max uF uV, uF})
    (hΔ : ∀ i, ∃ h : (Δ i).degree = d.shape.size i,
      F.canonicalTopologicalData.IsSegmentHead (Δ i) (h.symm ▸ d.blocks i))
    (ρ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier))
    (hρ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible ρ.representation)
    (hesi : letI := F.canonicalTopologicalData.topology
      F.canonicalTopologicalData.IsEssentiallySquareIntegrable ρ.representation)
    (D : F.canonicalTopologicalData.Segment.{max uF uV, uF})
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear D.degree F.Carrier))
    (hσ : F.canonicalTopologicalData.IsSegmentHead D σ) (hD : D.degree = t + 1)
    (hσρ : letI := F.canonicalTopologicalData.topology
      Nonempty ((F.canonicalTopologicalData.castRank hD σ).representation.Equiv
        ρ.representation))
    {P : ℂ[X]} (hP : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π ρ P) :
    lPolynomialPoleOrderAtZero P = poleLinkCount (Finset.univ.val.map Δ) D.dual := by
  classical
  let := F.canonicalTopologicalData.topology
  obtain ⟨eσ⟩ := hσρ
  obtain ⟨b, E, hd'⟩ := d.exists_withBlocks_isLanglandsQuotient.{uF, uV} hd
  obtain ⟨ρ₀, hρ₀, ⟨eρ⟩⟩ := padicIrreducibleSmoothSmallRealization.{uF, max uF uW, uW}
    p F F.canonicalTopologicalData (t + 1) ρ hρ
  have hesi₀ := (F.canonicalTopologicalData.isEssentiallySquareIntegrable_iff_of_equiv eρ).mp
    hesi
  let e := SquareIntegrableLanglandsDatum.single t.succ_pos ρ₀ hρ₀ hesi₀
  have he : e.IsLanglandsQuotient ρ :=
    SquareIntegrableLanglandsDatum.single_isLanglandsQuotient t.succ_pos ρ₀ hρ₀ hesi₀ ρ eρ.symm
  obtain ⟨P₀, Q, hP₀, hQ, hPQ⟩ := h95 p F ψ ν n t (d.withBlocks b E) e π ρ hd' he
  rw [hP.unique hP₀, hPQ, lPolynomialPoleOrderAtZero_prod _ _ fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j _ => (hQ i j).ne_zero, poleLinkCount_map_univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lPolynomialPoleOrderAtZero_prod _ _ fun j _ => (hQ i j).ne_zero]
  obtain ⟨h, hh⟩ := hΔ i
  have hj : ∀ j, lPolynomialPoleOrderAtZero (Q i j) =
      if SegmentPoleLink (Δ i) D.dual then 1 else 0 := fun j =>
    lPolynomialPoleOrderAtZero_of_segmentHeads_cast ν hSH h81 h81i hW (Δ i) D h hD
      (d.blocks i) σ hh hσ
      ((IsPadicRankLPolynomial.congr_equiv (E i).symm (eρ.symm.trans eσ.symm)).mp (hQ i j))
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  exact one_smul ℕ _

end RankinSelberg

end Langlands
