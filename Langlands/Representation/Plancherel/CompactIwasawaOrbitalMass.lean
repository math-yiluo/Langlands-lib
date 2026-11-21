import Langlands.Representation.Plancherel.ScaledIwasawaExchange
import Langlands.Analysis.Local.TwistedConjugationHaar

/-! # Comparing the compact Iwasawa masses by a central Levi orbital test -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Langlands.Plancherel.LeviInvariantIwasawaExchange

open Aubert.General Langlands.QuotientIntegration

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
  (K : OpenSubgroup G) (a : G)

/-- The pullback of the compact open indicator along the conjugacy map at `a`. -/
def compactConjugationIndicator (g : G) : ℝ≥0∞ :=
  (K : Set G).indicator 1 (g⁻¹ * a * g)

/-- The same compact condition on a radical, expressed using displacement by `a⁻¹`. -/
def compactConjugationPreimage (W : Subgroup G) : Set W :=
  {w | a⁻¹ * ((w : G)⁻¹ * a * w) ∈ K}

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {M W : Subgroup G}

private theorem measurable_compactConjugationIndicator :
    Measurable (compactConjugationIndicator K a) :=
  (measurable_one.indicator K.isOpen.measurableSet).comp
    ((continuous_inv.mul_const a).mul continuous_id).measurable

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
private theorem compactConjugationIndicator_left_invariant
    (ha : ∀ m : M, Commute (m : G) a) (m : M) (g : G) :
    compactConjugationIndicator K a ((m : G) * g) = compactConjugationIndicator K a g := by
  unfold compactConjugationIndicator
  congr 1
  have hm : (m : G)⁻¹ * a * m = a := by
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    exact (ha m).eq.symm
  calc
    _ = g⁻¹ * ((m : G)⁻¹ * a * m) * g := by group
    _ = _ := by rw [hm]

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
private theorem compactConjugationIndicator_mul
    (haK : a ∈ K) {k : G} (hk : k ∈ K) (w : W) :
    compactConjugationIndicator K a ((w : G) * k) =
      (compactConjugationPreimage K a W).indicator 1 w := by
  have he : ((w : G) * k)⁻¹ * a * ((w : G) * k) ∈ K ↔ (w : G)⁻¹ * a * w ∈ K := by
    change ((w : G) * k)⁻¹ * a * ((w : G) * k) ∈ K.toSubgroup ↔
      (w : G)⁻¹ * a * w ∈ K.toSubgroup
    have hnorm := (Subgroup.mem_normalizer_iff.mp
      (K.toSubgroup.le_normalizer (K.inv_mem hk))) ((w : G)⁻¹ * a * w)
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hnorm.symm
  have ha : (w : G)⁻¹ * a * w ∈ K ↔ w ∈ compactConjugationPreimage K a W :=
    (K.toSubgroup.mul_mem_cancel_left (K.inv_mem haK)).symm
  unfold compactConjugationIndicator
  by_cases hw : w ∈ compactConjugationPreimage K a W
  · rw [Set.indicator_of_mem ((he.trans ha).mpr hw), Set.indicator_of_mem hw,
      Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem (fun h => hw ((he.trans ha).mp h)), Set.indicator_of_notMem hw]

variable [MeasurableSpace W] [BorelSpace W]

private theorem measurableSet_compactConjugationPreimage :
    MeasurableSet (compactConjugationPreimage K a W) :=
  K.isOpen.measurableSet.preimage
    ((continuous_subtype_val.inv.mul_const a).mul continuous_subtype_val |>.const_mul a⁻¹).measurable

/-- If the displacement pushforward scales the radical measure and the
compact radical intersection has mass one, the preimage mass is that scale. -/
theorem measure_compactConjugationPreimage_of_map
    (β : W ≃ₜ* W) (hβ : ∀ w : W, ((β w : W) : G) = a⁻¹ * (w : G) * a)
    (μW : Measure W) (hnorm : μW {w : W | (w : G) ∈ K} = 1) (c : ℝ≥0∞)
    (hmap : μW.map (twistedConjugationMap β) = c • μW) :
    μW (compactConjugationPreimage K a W) = c := by
  let S : Set W := {w : W | (w : G) ∈ K}
  have hS : MeasurableSet S := K.isOpen.measurableSet.preimage continuous_subtype_val.measurable
  have hL : Measurable (twistedConjugationMap β) :=
    (β.continuous.inv.mul continuous_id).measurable
  have hpre : twistedConjugationMap β ⁻¹' S = compactConjugationPreimage K a W := by
    ext w
    change (((β w : W) : G)⁻¹ * (w : G) ∈ K) ↔ a⁻¹ * ((w : G)⁻¹ * a * w) ∈ K
    rw [hβ, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc, mul_assoc]
  have h := congrArg (fun ν : Measure W => ν S) hmap
  rw [Measure.map_apply hL hS, hpre, Measure.smul_apply, smul_eq_mul, hnorm, mul_one] at h
  exact h

variable [SecondCountableTopology G] [SecondCountableTopology W]

private theorem lintegral_iwasawaPush_compactConjugationIndicator
    (μG : Measure G) (μW : Measure W) [SFinite μW]
    (ha : ∀ m : M, Commute (m : G) a) (haK : a ∈ K) :
    ∫⁻ q, leviQuotientLift M (compactConjugationIndicator K a)
        (compactConjugationIndicator_left_invariant K a ha) q ∂iwasawaPush M μG K μW =
      μG (K : Set G) * μW (compactConjugationPreimage K a W) := by
  let Θ := compactConjugationIndicator K a
  let φ := leviQuotientLift M Θ (compactConjugationIndicator_left_invariant K a ha)
  have hΘ : Measurable Θ := measurable_compactConjugationIndicator K a
  have hφ : Measurable φ := measurable_leviQuotientLift M Θ hΘ _
  have hi := measurable_iwasawaCoordinates (M := M) (W := W)
  have hp : Measurable (fun p : G × W => φ (leviQuotientMk M ((p.2 : G) * p.1))) :=
    hφ.comp hi
  change ∫⁻ q, φ q ∂iwasawaPush M μG K μW = _
  rw [iwasawaPush, lintegral_map hφ hi, lintegral_prod _ hp.aemeasurable]
  calc
    _ = ∫⁻ k in (K : Set G), μW (compactConjugationPreimage K a W) ∂μG := by
      apply setLIntegral_congr_fun K.isOpen.measurableSet
      intro k hk
      change ∫⁻ w : W, Θ ((w : G) * k) ∂μW = _
      simp_rw [Θ, compactConjugationIndicator_mul K a haK hk]
      exact lintegral_indicator_one (measurableSet_compactConjugationPreimage K a)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]

variable {P P' U V : Subgroup G}
  [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (h : IsSemidirectDecomposition P M U) (h' : IsSemidirectDecomposition P' M V)
  (μM : Measure M) (μU : Measure U) (μV : Measure V)
  [μM.IsHaarMeasure] [μM.IsMulRightInvariant] [SFinite μM]
  [μU.IsHaarMeasure] [SFinite μU] [μV.IsHaarMeasure] [SFinite μV]

/-- An equal positive finite orbital mass for one compact central Levi point
forces equality of the two actual Iwasawa pushforwards. -/
theorem iwasawaExchangeRatio_eq_one_of_compactConjugation
    (μG : Measure G) [μG.IsHaarMeasure] [SFinite μG]
    (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
    (hK : IsCompact (K : Set G)) (hr : Continuous h.projection)
    (hr' : Continuous h'.projection)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hfac' : ∀ g : G, ∃ m : M, ∃ v : V, ∃ k ∈ K, g = (m : G) * v * k)
    (ha : ∀ m : M, Commute (m : G) a) (haK : a ∈ K)
    (heq : μV (compactConjugationPreimage K a V) = μU (compactConjugationPreimage K a U))
    (h0 : μU (compactConjugationPreimage K a U) ≠ 0)
    (hT : μU (compactConjugationPreimage K a U) ≠ ⊤) :
    iwasawaExchangeRatio K μM μU μV = 1 := by
  let φ := leviQuotientLift M (compactConjugationIndicator K a)
    (compactConjugationIndicator_left_invariant K a ha)
  have hU := lintegral_iwasawaPush_compactConjugationIndicator K a μG μU ha haK
  have hV := lintegral_iwasawaPush_compactConjugationIndicator K a μG μV ha haK
  change ∫⁻ q, φ q ∂iwasawaPush M μG K μU = _ at hU
  change ∫⁻ q, φ q ∂iwasawaPush M μG K μV = _ at hV
  rw [iwasawaPush_eq_ratio_smul h h' K μM μU μV hP hP' hK hr hr' hfac hfac',
    lintegral_smul_measure, smul_eq_mul, hU, heq] at hV
  exact (ENNReal.mul_eq_right (mul_ne_zero (K.isOpen.measure_ne_zero μG ⟨1, K.one_mem⟩) h0)
    (ENNReal.mul_ne_top hK.measure_ne_top hT)).mp hV

end Langlands.Plancherel.LeviInvariantIwasawaExchange
