import Langlands.Analysis.Local.QuotientNormalizingFunction

/-! # Passing a product integration formula to compatible left quotients -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory Set _root_.Topology
open scoped ENNReal

universe u v w

variable {G : Type u} {M : Type v} {X : Type w} [Group G] [Group M]
  (H : Subgroup G) (J : Subgroup M) (j : M →* G) (e : J ≃* H)
  (he : ∀ h : J, (e h : G) = j (h : M)) (k : X → G)

private theorem quotientMap_mul_mem (h : H) (g : G) :
    leftQuotientMap H (h.val * g) = leftQuotientMap H g := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp [mul_inv_rev]

/-- Product coordinates on a quotient, obtained by passing the first coordinate
through the left quotient by the corresponding subgroup. -/
def quotientFactorizationProductMap (p : LeftQuotient J × X) : LeftQuotient H :=
  descend J (fun m => leftQuotientMap H (j m * k p.2)) (fun h m => by
    rw [map_mul, mul_assoc, ← he h, quotientMap_mul_mem H (e h)]) p.1

@[simp]
theorem quotientFactorizationProductMap_mk (m : M) (x : X) :
    quotientFactorizationProductMap H J j e he k (leftQuotientMap J m, x) =
      leftQuotientMap H (j m * k x) := rfl

variable [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace X]
  [IsTopologicalGroup G] [IsTopologicalGroup M]

theorem continuous_quotientFactorizationProductMap
    (hj : Continuous j) (hk : Continuous k) :
    Continuous (quotientFactorizationProductMap H J j e he k) := by
  apply ((leftQuotient_isOpenQuotientMap J).prodMap
    (IsOpenQuotientMap.id (X := X))).isQuotientMap.continuous_iff.mpr
  change Continuous fun p : M × X => leftQuotientMap H (j p.1 * k p.2)
  exact (leftQuotient_isOpenQuotientMap H).continuous.comp
    ((hj.comp continuous_fst).mul (hk.comp continuous_snd))

variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space M] [LocallyCompactSpace M] [SecondCountableTopology M]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  [MeasurableSpace (LeftQuotient J)] [BorelSpace (LeftQuotient J)]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG]
  {μM : Measure M} [IsFiniteMeasureOnCompacts μM]
  {μH : Measure H} [IsFiniteMeasureOnCompacts μH] [μH.IsMulRightInvariant]
  {μJ : Measure J} [IsFiniteMeasureOnCompacts μJ] [μJ.IsMulRightInvariant]
  {νG : Measure (LeftQuotient H)} {νM : Measure (LeftQuotient J)}

/-- A product integration formula on the groups gives the same scalar multiple
of the compatible quotient measure after descent of the first coordinate. -/
theorem IsCompatible.map_quotientFactorizationProduct
    (hH : IsClosed (H : Set G)) (hJ : IsClosed (J : Set M))
    (hj : Continuous j) (hk : Continuous k) (hE : MeasurePreserving e μJ μH)
    (hG : IsCompatible H μG μH νG) (hM : IsCompatible J μM μJ νM)
    (ρ : Measure X) [SFinite ρ] (c : ℝ≥0∞)
    (hmap : (μM.prod ρ).map (fun p : M × X => j p.1 * k p.2) = c • μG)
    (r : G → ℝ≥0∞) (hr : IsNormalizingFunction H μH r) :
    (νM.prod ρ).map (quotientFactorizationProductMap H J j e he k) = c • νG := by
  have : LocallyCompactSpace (LeftQuotient J) := leftQuotient_locallyCompactSpace J
  have : SecondCountableTopology (LeftQuotient J) :=
    (leftQuotient_isOpenQuotientMap J).secondCountableTopology
  have : νM.Regular := hM.regular
  let φ : M × X → G := fun p => j p.1 * k p.2
  have hφ : Measurable φ := ((hj.comp continuous_fst).mul (hk.comp continuous_snd)).measurable
  let Ψ := quotientFactorizationProductMap H J j e he k
  have hΨ : Measurable Ψ := (continuous_quotientFactorizationProductMap H J j e he k hj hk).measurable
  have hq : Measurable (leftQuotientMap H) := (leftQuotient_isOpenQuotientMap H).continuous.measurable
  have hIntegral (f : LeftQuotient H → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ q, f q ∂(νM.prod ρ).map Ψ) = ∫⁻ q, f q ∂(c • νG) := by
    let F : G → ℝ≥0∞ := fun g => f (leftQuotientMap H g) * r g
    have hF : Measurable F := (hf.comp hq).mul hr.measurable
    have hFiber (x : X) :
        (∫⁻ m, F (φ (m, x)) ∂μM) = ∫⁻ q, f (Ψ (q, x)) ∂νM := by
      have hx : Measurable fun m : M => F (φ (m, x)) :=
        (hF.comp hφ).comp (measurable_id.prodMk measurable_const)
      rw [hM.lintegral_eq_lintegral_quotientAverageENNReal hJ _
        hx]
      apply lintegral_congr
      intro q
      induction q using Quotient.inductionOn with
      | h m =>
        rw [quotientAverageENNReal_mk]
        change (∫⁻ a : J, f (leftQuotientMap H (j (a.val * m) * k x)) *
          r (j (a.val * m) * k x) ∂μJ) = f (leftQuotientMap H (j m * k x))
        simp_rw [map_mul, mul_assoc, ← he, quotientMap_mul_mem]
        let b : G := j m * k x
        have hb : Measurable (fun h : H => r (h.val * b)) :=
          hr.measurable.comp (continuous_subtype_val.mul_const b).measurable
        have hbe : Measurable (fun a : J => r ((e a).val * b)) :=
          hb.comp hE.measurable
        change (∫⁻ a : J, f (leftQuotientMap H b) * r ((e a).val * b) ∂μJ) = _
        rw [lintegral_const_mul _ hbe,
          ← lintegral_map hb hE.measurable, hE.map_eq, hr.lintegral_eq_one, mul_one]
    have hDesc : (∫⁻ g, F g ∂μG) = ∫⁻ q, f q ∂νG := by
      rw [hG.lintegral_eq_lintegral_quotientAverageENNReal hH F hF]
      apply lintegral_congr
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        rw [quotientAverageENNReal_mk]
        change (∫⁻ a : H, f (leftQuotientMap H (a.val * g)) * r (a.val * g) ∂μH) = _
        simp_rw [quotientMap_mul_mem]
        have hg : Measurable fun a : H => r (a.val * g) :=
          hr.measurable.comp (continuous_subtype_val.mul_const g).measurable
        rw [lintegral_const_mul _ hg, hr.lintegral_eq_one, mul_one]
        rfl
    calc
      (∫⁻ q, f q ∂(νM.prod ρ).map Ψ) = ∫⁻ p, f (Ψ p) ∂νM.prod ρ :=
        lintegral_map hf hΨ
      _ = ∫⁻ x, ∫⁻ q, f (Ψ (q, x)) ∂νM ∂ρ :=
        lintegral_prod_symm _ (hf.comp hΨ).aemeasurable
      _ = ∫⁻ x, ∫⁻ m, F (φ (m, x)) ∂μM ∂ρ :=
        lintegral_congr fun x => (hFiber x).symm
      _ = ∫⁻ p, F (φ p) ∂μM.prod ρ :=
        (lintegral_prod_symm _ (hF.comp hφ).aemeasurable).symm
      _ = ∫⁻ g, F g ∂(μM.prod ρ).map φ := (lintegral_map hF hφ).symm
      _ = ∫⁻ q, f q ∂(c • νG) := by
        change (μM.prod ρ).map φ = c • μG at hmap
        rw [hmap, lintegral_smul_measure, lintegral_smul_measure, hDesc]
  ext s hs
  simpa only [lintegral_indicator_one hs] using hIntegral (s.indicator 1)
    (measurable_one.indicator hs)

end Langlands.QuotientIntegration
