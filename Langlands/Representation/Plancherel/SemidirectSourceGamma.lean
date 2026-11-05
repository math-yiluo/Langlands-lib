import Langlands.Representation.Aubert.General.SemidirectHaarModulus
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicHaar
import Mathlib.MeasureTheory.Group.LIntegral

/-! # The source open-cell constant in canonical semidirect coordinates -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hp : Continuous h.projection)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
include h in
/-- The canonical semidirect multiplication has values in the actual parabolic. -/
theorem semidirectCoordMem (x : M × U) :
    leviUnipotentMul x ∈ P :=
  P.mul_mem (h.levi_le x.1.property) (h.unipotent_le x.2.property)

include hp in
/-- Reuse the existing canonical semidirect homeomorphism for the exact
coordinate map used by the source Haar integration engine. -/
theorem isHomeomorph_leviUnipotentCoord_semidirect :
    IsHomeomorph (leviUnipotentCoord (semidirectCoordMem h)) :=
  (h.coordinates hp).isHomeomorph

variable [MeasurableSpace G] [BorelSpace G]

/-- The source parabolic measure is the actual product Haar pushforward in
the already constructed canonical Levi-then-radical coordinates. -/
def semidirectSourceParabolicMeasure (μM : Measure M) (μU : Measure U) : Measure P :=
  (μM.prod μU).map (h.coordinates hp)

omit [BorelSpace G] in
/-- The canonical product pushforward is exactly the published Haar engine's
measure, with no unspecified scalar comparison. -/
theorem semidirectSourceParabolicMeasure_eq (μM : Measure M) (μU : Measure U) :
    semidirectSourceParabolicMeasure h hp μM μU =
      leviUnipotentMeasure (semidirectCoordMem h) μM μU := rfl

variable [SecondCountableTopology U]
  (μM : Measure M) [SFinite μM] [μM.IsHaarMeasure]
  (μU : Measure U) [SFinite μU] [μU.IsHaarMeasure]

/-- Haar invariance is imported through the actual canonical coordinates,
rather than assumed for an independently chosen measure on `P`. -/
theorem semidirectSourceParabolicMeasure_isHaarMeasure :
    (semidirectSourceParabolicMeasure h hp μM μU).IsHaarMeasure := by
  rw [semidirectSourceParabolicMeasure_eq]
  exact leviUnipotentMeasure_isHaarMeasure h.levi_le_normalizer
    (semidirectCoordMem h) μM μU (isHomeomorph_leviUnipotentCoord_semidirect h hp)

omit [SFinite μM] [μM.IsHaarMeasure] [μU.IsHaarMeasure] in
/-- The same normalized Levi and radical measures normalize the actual
parabolic measure when their compact intersections factor. -/
theorem semidirectSourceParabolicMeasure_compact (K : OpenSubgroup G)
    (hKsplit : ∀ (m : M) (u : U),
      (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μM {m : M | (m : G) ∈ K} = 1)
    (hUK : μU {u : U | (u : G) ∈ K} = 1) :
    semidirectSourceParabolicMeasure h hp μM μU {p : P | (p : G) ∈ K} = 1 := by
  rw [semidirectSourceParabolicMeasure_eq]
  have ht := leviUnipotentMeasure_inter (semidirectCoordMem h) μM μU
    (K := K.toSubgroup) K.isOpen.measurableSet hKsplit
  change (leviUnipotentMeasure (semidirectCoordMem h) μM μU) {p : P | (p : G) ∈ K} =
    μM {m : M | (m : G) ∈ K} * μU {u : U | (u : G) ∈ K} at ht
  rw [hMK, hUK, one_mul] at ht
  exact ht

variable {V : Subgroup G}

/-- The actual source open-cell integral using canonical semidirect product
Haar measure. It is not a scalar chosen to force an integration identity. -/
def semidirectSourceGamma (μV : Measure V) (K : Subgroup G) : ℝ≥0∞ :=
  openCellConstant (semidirectSourceParabolicMeasure h hp μM μU) μV K

omit [BorelSpace G] [SecondCountableTopology U]
  [SFinite μM] [μM.IsHaarMeasure] [SFinite μU] [μU.IsHaarMeasure] in
/-- The source gamma is the already published open-cell constant for the
same exact Levi-then-radical measure. -/
theorem semidirectSourceGamma_eq (μV : Measure V) (K : Subgroup G) :
    semidirectSourceGamma h hp μM μU μV K =
      openCellConstant (leviUnipotentMeasure (semidirectCoordMem h) μM μU) μV K := rfl

section Iwasawa

variable (K : OpenSubgroup G)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- One actual parabolic factor in `G = P K`. The resulting modulus integral
is identified below with the choice-free open-cell constant. -/
def sourceIwasawaParabolicFactor (g : G) : P :=
  Classical.choose (hPK g)

/-- The canonical actual semidirect coordinates of the chosen parabolic factor. -/
def sourceIwasawaCoordinates (g : G) : M × U :=
  (h.coordinates hp).symm (sourceIwasawaParabolicFactor K hPK g)

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology U] in
theorem sourceIwasawaCoordinates_spec (g : G) :
    (leviUnipotentMul (sourceIwasawaCoordinates h hp K hPK g))⁻¹ * g ∈ K := by
  obtain ⟨k, hk⟩ := Classical.choose_spec (hPK g)
  have hcoord : leviUnipotentMul (sourceIwasawaCoordinates h hp K hPK g) =
      (sourceIwasawaParabolicFactor K hPK g : G) :=
    congrArg (fun p : P => (p : G)) ((h.coordinates hp).apply_symm_apply _)
  rw [hcoord]
  change g = (sourceIwasawaParabolicFactor K hPK g : G) * (k : G) at hk
  have heq : (sourceIwasawaParabolicFactor K hPK g : G)⁻¹ * g = (k : G) := by
    calc
      _ = (sourceIwasawaParabolicFactor K hPK g : G)⁻¹ *
          ((sourceIwasawaParabolicFactor K hPK g : G) * (k : G)) :=
        congrArg (fun a : G => (sourceIwasawaParabolicFactor K hPK g : G)⁻¹ * a) hk
      _ = _ := inv_mul_cancel_left _ _
  rw [heq]
  exact k.property

end Iwasawa

section ModulusIntegral

variable [LocallyCompactSpace G] (hU : IsClosed (U : Set G))
  [μM.IsMulRightInvariant] [μU.IsMulRightInvariant]
  (μV : Measure V)
  (K : OpenSubgroup G)
  (hKsplit : ∀ (m : M) (u : U),
    (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
  (hMK : μM {m : M | (m : G) ∈ K} = 1)
  (hUK : μU {u : U | (u : G) ∈ K} = 1)

omit [SFinite μU] [μU.IsMulRightInvariant] in
/-- The conjugation modulus premise of the source engine is the actual
closed-subgroup Haar character of the canonical normalization. -/
theorem isConjModulus_semidirect_closedCharacter :
    IsConjModulus h.levi_le_normalizer μU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [HaarModulus.closedRestrictCharacter_eq]
  exact isConjModulus_restrictCharacter h.levi_le_normalizer μU

omit [μM.IsHaarMeasure] in
include hKsplit hMK hUK in
/-- Any actual Iwasawa component gives the same gamma integral; its modulus
is the existing actual closed-subgroup character. -/
theorem semidirectSourceGamma_eq_lintegral_of_coordinates
    (ℓ : V → M × U)
    (hℓ : ∀ v : V, (leviUnipotentMul (ℓ v))⁻¹ * (v : G)⁻¹ ∈ K) :
    semidirectSourceGamma h hp μM μU μV K =
      ∫⁻ v, ((HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
        (ℓ v).1 : ℝ≥0) : ℝ≥0∞) ∂μV := by
  rw [semidirectSourceGamma_eq]
  exact openCellConstant_leviUnipotentMeasure h.levi_le_normalizer
    (semidirectCoordMem h) μM μU μV
    (isHomeomorph_leviUnipotentCoord_semidirect h hp)
    (isConjModulus_semidirect_closedCharacter h μU hU)
    K.isOpen.measurableSet hKsplit hMK hUK ℓ hℓ

omit [μM.IsHaarMeasure] in
include hKsplit hMK hUK in
/-- With inversion-invariant opposite-radical Haar measure, gamma is the
literal source integral `∫ δ_P(m_P(v)) dv` of I.1 (3). -/
theorem semidirectSourceGamma_eq_iwasawa_integral [μV.IsInvInvariant]
    (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G)) :
    semidirectSourceGamma h hp μM μU μV K =
      ∫⁻ v : V, ((HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
        (sourceIwasawaCoordinates h hp K hPK v).1 : ℝ≥0) : ℝ≥0∞) ∂μV := by
  rw [semidirectSourceGamma_eq_lintegral_of_coordinates h hp μM μU hU μV K
    hKsplit hMK hUK (fun v : V => sourceIwasawaCoordinates h hp K hPK (v : G)⁻¹)
    (fun v => sourceIwasawaCoordinates_spec h hp K hPK (v : G)⁻¹)]
  exact lintegral_inv_eq_self (μ := μV) (fun v : V =>
    ((HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
      (sourceIwasawaCoordinates h hp K hPK v).1 : ℝ≥0) : ℝ≥0∞))

end ModulusIntegral

section OpenCell

variable [LocallyCompactSpace P] [LocallyCompactSpace V]
  [SecondCountableTopology P] [SecondCountableTopology V]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (μV : Measure V) [μV.IsHaarMeasure]
  (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
  (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

include μ hι hnull hK in
/-- The actual source gamma is positive and finite under the displayed
open-cell hypotheses; these geometric obligations are not inferred from
the semidirect decomposition. -/
theorem semidirectSourceGamma_ne_zero_ne_top :
    semidirectSourceGamma h hp μM μU μV K ≠ 0 ∧
      semidirectSourceGamma h hp μM μU μV K ≠ ⊤ := by
  let := semidirectSourceParabolicMeasure_isHaarMeasure h hp μM μU
  have hK0 : μ (K : Set G) ≠ 0 := K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKtop : μ (K : Set G) ≠ ⊤ := hK.measure_lt_top.ne
  have ht := lintegral_eq_openCellConstant_inv_mul μ
    (semidirectSourceParabolicMeasure h hp μM μU) μV hι hnull
    K.isOpen.measurableSet hK0 hKtop
  exact ⟨ht.1, ht.2.1⟩

include hι hnull hK in
/-- The open-cell integration formula uses this same actual gamma and
product measure, retaining the displayed ambient compact Haar mass. -/
theorem lintegral_eq_semidirectSourceGamma_inv_mul
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g, F g ∂μ) =
      μ (K : Set G) * (semidirectSourceGamma h hp μM μU μV K)⁻¹ *
        ∫⁻ m, ∫⁻ u, ∫⁻ v, F ((m : G) * u * (v : G)⁻¹) ∂μV ∂μU ∂μM := by
  rw [semidirectSourceGamma_eq]
  exact lintegral_eq_openCell_levi_unipotent h.levi_le_normalizer
    (semidirectCoordMem h) μ μM μU μV
    (isHomeomorph_leviUnipotentCoord_semidirect h hp)
    hι hnull K.isOpen.measurableSet
    (K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩) hK.measure_lt_top.ne F hF

include hι hnull hK in
/-- Under the source ambient normalization, the factor in the formula is
exactly gamma inverse, with no residual ambient Haar mass. -/
theorem lintegral_eq_semidirectSourceGamma_normalized
    (hμK : μ (K : Set G) = 1) (F : G → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g, F g ∂μ) =
      (semidirectSourceGamma h hp μM μU μV K)⁻¹ *
        ∫⁻ m, ∫⁻ u, ∫⁻ v, F ((m : G) * u * (v : G)⁻¹) ∂μV ∂μU ∂μM := by
  simpa only [hμK, one_mul] using lintegral_eq_semidirectSourceGamma_inv_mul
    h hp μM μU μ μV hι hnull K hK F hF

end OpenCell

end Langlands.Plancherel
