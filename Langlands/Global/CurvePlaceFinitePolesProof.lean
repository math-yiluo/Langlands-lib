/-
The valuation-subring comparison adapts the corresponding proof in
`Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra`, ported from
Anthropic's Lean formalization of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Copyright 2026 Anthropic, PBC,
under Apache-2.0. See `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and
`ATTRIBUTION.md`. Modified by Worker 208: use explicit separability to
obtain the Dedekind instance in all characteristics and combine two charts
with a separating generator over arbitrary perfect constants.
-/
import Langlands.Global.CurvePlaceFinitePolesStatement
import Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-! # Finite poles on actual function-field curve places -/

noncomputable section
universe u

open IntermediateField Polynomial IsDedekindDomain AlgebraicCurve
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin

namespace Langlands.Global

section Separating

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] [PerfectField k]

private theorem exists_separating_generator :
    ∃ s : F, Transcendental k s ∧ FiniteDimensional k⟮s⟯ F ∧
      Algebra.IsSeparable k⟮s⟯ F := by
  let : Algebra.EssFiniteType k[X] (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors k[X])
  let : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k k[X] (RatFunc k)
  let : Algebra.EssFiniteType k F :=
    Algebra.EssFiniteType.comp k (RatFunc k) F
  obtain ⟨s, hb, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  have hpoly : IsTranscendenceBasis k (fun _ : Unit => (Polynomial.X : k[X])) :=
    IsTranscendenceBasis.polynomial Unit k
  let : Algebra.IsAlgebraic k[X] (RatFunc k) :=
    IsLocalization.isAlgebraic (RatFunc k) (nonZeroDivisors k[X])
  have hrat := hpoly.algebraMap_comp (A := RatFunc k)
  have hfield := hrat.algebraMap_comp (A := F)
  have hcard : s.card = 1 := by
    have h := hb.lift_cardinalMk_eq hfield
    simpa using h
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
  have ht : Transcendental k t := hb.1.transcendental ⟨t, by simp⟩
  have hcoe : (({t} : Finset F) : Set F) = {t} := Finset.coe_singleton t
  rw [hcoe] at hsep
  exact ⟨t, ht, FunctionField.finiteDimensional_of_adjoin_transcendental ht,
    hsep⟩


end Separating

section Chart

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  (s : F) [FiniteDimensional k⟮s⟯ F] [Algebra.IsSeparable k⟮s⟯ F]

local instance separatingChartDedekind :
    IsDedekindDomain (CurveModel.chartRing k ({s} : Set F)) :=
  IsIntegralClosure.isDedekindDomain (Algebra.adjoin k ({s} : Set F)) k⟮s⟯ F _

private theorem separatingChart_valuationSubringAtPrime_le
    (O : ValuationSubring F) (hK : ∀ a : k, algebraMap k F a ∈ O)
    (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime F
      (CurveModel.primeOfValuationSubring k s O hK hs hO) ≤ O := by
  intro x hx
  have hx' : ∃ (a b : CurveModel.chartRing k ({s} : Set F))
      (_ : b ∈ (CurveModel.centre k s O hK hs).primeCompl),
      x = algebraMap _ F a * (algebraMap _ F b)⁻¹ := hx
  obtain ⟨a, b, hb, rfl⟩ := hx'
  apply O.mem_of_valuation_le_one
  rw [map_mul, map_inv₀, show O.valuation (algebraMap _ F b) = 1 from
    CurveModel.valuation_eq_one_of_not_mem_centre k s O hK hs hb, inv_one, mul_one]
  exact CurveModel.valuation_coe_le_one k s O hK hs a

private theorem separatingChart_valuationSubringAtPrime_eq
    (O : ValuationSubring F) (hK : ∀ a : k, algebraMap k F a ∈ O)
    (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime F
      (CurveModel.primeOfValuationSubring k s O hK hs hO) = O :=
  ValuationSubring.eq_of_le_of_ne_top _
    (separatingChart_valuationSubringAtPrime_le k F s O hK hs hO) hO

private theorem separatingChart_exists_prime (v : Place k F)
    (hs : s ∈ v.toValuationSubring) :
    ∃ p : HeightOneSpectrum (CurveModel.chartRing k ({s} : Set F)),
      Place.ofHeightOneSpectrum (K := k) p = v := by
  refine ⟨CurveModel.primeOfValuationSubring k s v.toValuationSubring
    v.algebraMap_mem' hs v.ne_top', ?_⟩
  apply Place.ext
  rw [Place.ofHeightOneSpectrum_toValuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact separatingChart_valuationSubringAtPrime_eq k F s _ _ hs _

private theorem finite_separatingChart_poles (x : F) :
    {v : Place k F | s ∈ v.toValuationSubring ∧ x ∉ v.toValuationSubring}.Finite := by
  have h := (HeightOneSpectrum.Support.finite
    (CurveModel.chartRing k ({s} : Set F)) x).image
      (Place.ofHeightOneSpectrum (K := k) (F := F))
  apply h.subset
  rintro v ⟨hs, hx⟩
  obtain ⟨p, rfl⟩ := separatingChart_exists_prime k F s v hs
  refine ⟨p, ?_, rfl⟩
  change 1 < p.valuation F x
  rw [Place.ofHeightOneSpectrum_toValuationSubring,
    Valuation.mem_valuationSubring_iff] at hx
  exact lt_of_not_ge hx


end Chart

theorem curvePlaceFinitePoles : CurvePlaceFinitePolesStatement.{u} := by
  intro k F _ _ _ _ _ _ _ x
  obtain ⟨s, _, hfin, hsep⟩ := exists_separating_generator k F
  let : FiniteDimensional k⟮s⟯ F := hfin
  let : Algebra.IsSeparable k⟮s⟯ F := hsep
  have hinv : k⟮s⁻¹⟯ = k⟮s⟯ :=
    le_antisymm
      (adjoin_simple_le_iff.mpr (inv_mem (mem_adjoin_simple_self k s)))
      (adjoin_simple_le_iff.mpr (by
        simpa using inv_mem (mem_adjoin_simple_self k s⁻¹)))
  let : FiniteDimensional k⟮s⁻¹⟯ F := by rw [hinv]; infer_instance
  let : Algebra.IsSeparable k⟮s⁻¹⟯ F := by rw [hinv]; infer_instance
  apply ((finite_separatingChart_poles k F s x).union
    (finite_separatingChart_poles k F s⁻¹ x)).subset
  intro v hx
  rcases v.toValuationSubring.mem_or_inv_mem s with hs | hs
  · exact Or.inl ⟨hs, hx⟩
  · exact Or.inr ⟨hs, hx⟩


end Langlands.Global
