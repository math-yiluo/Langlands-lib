import Langlands.Representation.Plancherel.SemidirectSourceGamma
import Langlands.Representation.Plancherel.NormalizedCompactPicture
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical

/-! # Regularity and real integration of the actual source gamma integrand -/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hp : Continuous h.projection)
  (hU : IsClosed (U : Set G)) (K : OpenSubgroup G)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

include hPK in
omit [NonarchimedeanGroup G] [LocallyCompactSpace G] in
/-- The supplied actual subgroup factorization, in the existing spherical-weight interface. -/
theorem sourceIwasawaPair : IsIwasawaPair P K.toSubgroup := by
  intro g
  obtain ⟨p, k, hg⟩ := hPK g
  exact ⟨p, p.property, k, k.property, hg⟩

/-- The actual Levi conjugation modulus at the chosen source Iwasawa component. -/
def sourceIwasawaModulus (g : G) : ℝ :=
  ((HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
    (sourceIwasawaCoordinates h hp K hPK g).1 : ℝ≥0) : ℝ)

theorem sourceIwasawaModulus_pos (g : G) :
    0 < sourceIwasawaModulus h hp hU K hPK g := by
  unfold sourceIwasawaModulus
  exact_mod_cast pos_iff_ne_zero.mpr (Units.ne_zero _)

section Regularity

variable (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G))

include hp hP hK in
/-- The actual Levi modulus pulled back to `P` is trivial on `P ∩ K`. -/
theorem sourceIwasawaCharacter_compact (p : P) (hpk : (p : G) ∈ K) :
    ((HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer).comp
      h.projection) p = 1 := by
  have hpk' : p ∈ Induction.conjOpenSubgroup P K 1 := by
    simpa only [Induction.mem_conjOpenSubgroup, inv_one, one_mul, mul_one] using hpk
  exact eq_one_of_isOpen_ker_of_isCompact
    ((HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer).comp h.projection)
    ((HaarModulus.isOpen_ker_closedRestrictCharacter U hU M
      h.levi_le_normalizer).preimage hp)
    (Induction.isCompact_conjOpenSubgroup P hP K hK 1) hpk'

include hP hK in
/-- A square of the already regular spherical weight gives the actual scalar
modulus, although the chosen Iwasawa factors need not be continuous. -/
theorem sourceIwasawaModulus_eq_weight_sq (g : G) :
    sourceIwasawaModulus h hp hU K hPK g =
      iwasawaWeight (sourceIwasawaPair K hPK)
        ((HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer).comp
          h.projection) g ^ 2 := by
  obtain ⟨k, hk⟩ := Classical.choose_spec (hPK g)
  have hw := iwasawaWeight_mul (hPK := sourceIwasawaPair K hPK)
    (sourceIwasawaCharacter_compact h hp hU K hP hK)
    (sourceIwasawaParabolicFactor K hPK g).property k.property
  change g = (sourceIwasawaParabolicFactor K hPK g : G) * (k : G) at hk
  rw [← hk] at hw
  rw [hw, sourceIwasawaModulus, pow_two, ← NNReal.coe_mul, NNReal.mul_self_sqrt]
  rfl

include hP hK in
theorem isLocallyConstant_sourceIwasawaModulus :
    IsLocallyConstant (sourceIwasawaModulus h hp hU K hPK) := by
  have heq : sourceIwasawaModulus h hp hU K hPK = fun g =>
      iwasawaWeight (sourceIwasawaPair K hPK)
        ((HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer).comp
          h.projection) g ^ 2 :=
    funext (sourceIwasawaModulus_eq_weight_sq h hp hU K hPK hP hK)
  rw [heq]
  exact (isLocallyConstant_iwasawaWeight
    (sourceIwasawaCharacter_compact h hp hU K hP hK) K.isOpen).comp (fun r : ℝ => r ^ 2)

include hP hK in
theorem continuous_sourceIwasawaModulus :
    Continuous (sourceIwasawaModulus h hp hU K hPK) :=
  (isLocallyConstant_sourceIwasawaModulus h hp hU K hPK hP hK).continuous

end Regularity

section Integration

variable [MeasurableSpace G] [BorelSpace G] {V : Subgroup G}
  [SecondCountableTopology U]
  (μM : Measure M) [SFinite μM] [μM.IsHaarMeasure]
  (μU : Measure U) [SFinite μU] [μU.IsHaarMeasure]
  (μV : Measure V)

/-- The real value of the same exact open-cell constant, without rescaling. -/
def semidirectSourceGammaReal : ℝ :=
  (semidirectSourceGamma h hp μM μU μV K).toReal

variable [μM.IsMulRightInvariant] [μU.IsMulRightInvariant] [μV.IsInvInvariant]
  (hKsplit : ∀ (m : M) (u : U),
    (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
  (hMK : μM {m : M | (m : G) ∈ K} = 1)
  (hUK : μU {u : U | (u : G) ∈ K} = 1)

include hKsplit hMK hUK in
omit [μM.IsHaarMeasure] in
/-- The earlier lower-integral identity concerns this precise nonnegative
real-valued function. No measurability of a component map is an input. -/
theorem semidirectSourceGamma_eq_lintegral_ofReal :
    semidirectSourceGamma h hp μM μU μV K =
      ∫⁻ v : V, ENNReal.ofReal (sourceIwasawaModulus h hp hU K hPK v) ∂μV := by
  rw [semidirectSourceGamma_eq_iwasawa_integral h hp μM μU hU μV K
    hKsplit hMK hUK hPK]
  simp only [sourceIwasawaModulus, ENNReal.ofReal_coe_nnreal]

variable (hP : IsClosed (P : Set G))
  [LocallyCompactSpace P] [LocallyCompactSpace V]
  [SecondCountableTopology P] [SecondCountableTopology V]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [μV.IsHaarMeasure]
  (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
  (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
  (hK : IsCompact (K : Set G))

include hP μ hι hnull hK hKsplit hMK hUK in
/-- Genuine Bochner integrability follows from scalar regularity and the
proved finiteness of the same lower integral. -/
theorem integrable_sourceIwasawaModulus :
    Integrable (fun v : V => sourceIwasawaModulus h hp hU K hPK v) μV := by
  refine ⟨((continuous_sourceIwasawaModulus h hp hU K hPK hP hK).comp
    continuous_subtype_val).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun v : V =>
      (sourceIwasawaModulus_pos h hp hU K hPK v).le),
    ← semidirectSourceGamma_eq_lintegral_ofReal h hp hU K hPK μM μU μV
      hKsplit hMK hUK]
  exact lt_top_iff_ne_top.mpr
    (semidirectSourceGamma_ne_zero_ne_top h hp μM μU μ μV hι hnull K hK).2

include hP μ hι hnull hK hKsplit hMK hUK in
/-- The literal source real integral is convergent and equals the original
open-cell constant's real value. -/
theorem semidirectSourceGammaReal_eq_integral :
    semidirectSourceGammaReal h hp K μM μU μV =
      ∫ v : V, sourceIwasawaModulus h hp hU K hPK v ∂μV := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun v : V =>
      (sourceIwasawaModulus_pos h hp hU K hPK v).le)
    (integrable_sourceIwasawaModulus h hp hU K hPK μM μU μV
      hKsplit hMK hUK hP μ hι hnull hK).aestronglyMeasurable,
    ← semidirectSourceGamma_eq_lintegral_ofReal h hp hU K hPK μM μU μV
      hKsplit hMK hUK]
  rfl

include μ hι hnull hK in
omit [LocallyCompactSpace G] [μM.IsMulRightInvariant] [μU.IsMulRightInvariant]
  [μV.IsInvInvariant] in
/-- The real gamma is strictly positive, with its original Haar scale. -/
theorem semidirectSourceGammaReal_pos :
    0 < semidirectSourceGammaReal h hp K μM μU μV := by
  obtain ⟨h0, ht⟩ :=
    semidirectSourceGamma_ne_zero_ne_top h hp μM μU μ μV hι hnull K hK
  exact ENNReal.toReal_pos h0 ht

end Integration

end Langlands.Plancherel
