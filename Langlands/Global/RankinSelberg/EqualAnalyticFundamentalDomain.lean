import Langlands.Global.LeftCosetMeasure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Integral

/-! # Central translation of fundamental domains and a fibration formula

Let `Γ` be a countable subgroup of a group `G` with a left invariant measure `μ`, and let `s` be
a measurable fundamental domain for the left action of `Γ`.

* Left translation by a central element `b` maps `s` to a fundamental domain, so integrals of
  `Γ`-invariant functions over `s` are unchanged by `x ↦ b x` (`setLIntegral_comp_mul_left`,
  `setIntegral_comp_mul_left`, `measure_inter_preimage_mul_left`).
* **Fibration over a central family.** Let `ζ : A → G` take central values and let `ν` be a
  measure on `A` and `t ⊆ A` be such that every fiber `{a ∈ t | ζ(a)⁻¹ g ∈ S}` of a `Γ`-invariant
  set `S` has `ν`-measure one. Then `∫_s f = ∫_(s ∩ S) ∫_t f(ζ(a) g) dν(a) dμ(g)` for every
  `Γ`-invariant `f ≥ 0` (`lintegral_eq_lintegral_fibration`), and the quotient measure of `s` is
  the image of `μ|_(s ∩ S) ⊗ ν|_t` under `(g, a) ↦ Γ ζ(a) g`
  (`quotientMeasure_eq_map_fibration`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
  (μ : Measure G) [μ.IsMulLeftInvariant]

omit [MeasurableSpace G] [MeasurableMul G] in
theorem inv_mul_comm_of_central {b : G} (hb : ∀ g : G, b * g = g * b) (g : G) :
    b⁻¹ * g = g * b⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hb g, mul_assoc, mul_inv_cancel, mul_one]

/-- Left translation by a central element maps fundamental domains to fundamental domains. -/
theorem isFundamentalDomain_preimage_mul_left {s : Set G} (hs : IsFundamentalDomain Γ s μ)
    (b : G) (hb : ∀ g : G, b * g = g * b) :
    IsFundamentalDomain Γ ((fun x => b * x) ⁻¹' s) μ :=
  hs.preimage_of_equiv (measurePreserving_mul_left μ b).quasiMeasurePreserving
    Function.bijective_id fun γ x => by
      show b * ((γ : G) * x) = (γ : G) * (b * x)
      rw [← mul_assoc, hb, mul_assoc]

variable [Countable Γ]

/-- The measure of a `Γ`-invariant set inside a fundamental domain is unchanged by left
translation by a central element. -/
theorem measure_inter_preimage_mul_left {s : Set G} (hs : IsFundamentalDomain Γ s μ)
    (b : G) (hb : ∀ g : G, b * g = g * b) {T : Set G} (hT : MeasurableSet T)
    (hTΓ : ∀ (γ : Γ) (x : G), (γ : G) * x ∈ T ↔ x ∈ T) :
    μ (s ∩ (fun x => b * x) ⁻¹' T) = μ (s ∩ T) := by
  have hfd := isFundamentalDomain_preimage_mul_left Γ μ hs b⁻¹ (inv_mul_comm_of_central hb)
  have h1 : μ (s ∩ (fun x => b * x) ⁻¹' T) =
      μ ((fun x => b⁻¹ * x) ⁻¹' (s ∩ (fun x => b * x) ⁻¹' T)) :=
    (measure_preimage_mul μ b⁻¹ _).symm
  have h2 : (fun x => b⁻¹ * x) ⁻¹' (s ∩ (fun x => b * x) ⁻¹' T) =
      T ∩ (fun x => b⁻¹ * x) ⁻¹' s := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mul_inv_cancel_left]
    exact and_comm
  rw [h1, h2, hfd.measure_set_eq hs hT (fun γ => by ext x; exact hTΓ γ x), inter_comm]

/-- **Central translation of a set integral.** -/
theorem setLIntegral_comp_mul_left {s : Set G} (hs : IsFundamentalDomain Γ s μ)
    (hsm : MeasurableSet s) (b : G) (hb : ∀ g : G, b * g = g * b) (f : G → ℝ≥0∞)
    (hfΓ : ∀ (γ : Γ) (x : G), f ((γ : G) * x) = f x) :
    ∫⁻ x in s, f (b * x) ∂μ = ∫⁻ x in s, f x ∂μ := by
  have hfd := isFundamentalDomain_preimage_mul_left Γ μ hs b⁻¹ (inv_mul_comm_of_central hb)
  have hsm' : MeasurableSet ((fun x => b⁻¹ * x) ⁻¹' s) := hsm.preimage (measurable_const_mul _)
  have h1 : ∫⁻ x in s, f (b * x) ∂μ =
      ∫⁻ x, ((fun x => b⁻¹ * x) ⁻¹' s).indicator f (b * x) ∂μ := by
    rw [← lintegral_indicator hsm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, indicator_of_mem (by simpa using hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (by simpa using hx)]
  rw [h1, lintegral_mul_left_eq_self, lintegral_indicator hsm']
  exact hfd.setLIntegral_eq hs f fun γ x => hfΓ γ x

/-- **Central translation of a Bochner set integral.** -/
theorem setIntegral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set G} (hs : IsFundamentalDomain Γ s μ) (hsm : MeasurableSet s) (b : G)
    (hb : ∀ g : G, b * g = g * b) (f : G → E)
    (hfΓ : ∀ (γ : Γ) (x : G), f ((γ : G) * x) = f x) :
    ∫ x in s, f (b * x) ∂μ = ∫ x in s, f x ∂μ := by
  have hfd := isFundamentalDomain_preimage_mul_left Γ μ hs b⁻¹ (inv_mul_comm_of_central hb)
  have hsm' : MeasurableSet ((fun x => b⁻¹ * x) ⁻¹' s) := hsm.preimage (measurable_const_mul _)
  have h1 : ∫ x in s, f (b * x) ∂μ =
      ∫ x, ((fun x => b⁻¹ * x) ⁻¹' s).indicator f (b * x) ∂μ := by
    rw [← integral_indicator hsm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, indicator_of_mem (by simpa using hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (by simpa using hx)]
  rw [h1, integral_mul_left_eq_self (fun y => ((fun x => b⁻¹ * x) ⁻¹' s).indicator f y) b,
    integral_indicator hsm']
  exact hfd.setIntegral_eq hs fun γ x => hfΓ γ x

/-! ### Fibration over a central family -/

section Fibration

variable [MeasurableMul₂ G] [MeasurableInv G] [SFinite μ] {A : Type*} [MeasurableSpace A]
  (ν : Measure A) [SFinite ν] (ζ : A → G)

/-- **Fibration over a central family.** If `ζ` is measurable with central values and every
fiber `t ∩ {a | ζ(a)⁻¹ g ∈ S}` of the `Γ`-invariant set `S` has `ν`-measure one, then for every
measurable `Γ`-invariant `f ≥ 0`, `∫_s f dμ = ∫_(s ∩ S) ∫_t f (ζ(a) g) dν(a) dμ(g)`. -/
theorem lintegral_eq_lintegral_fibration {s : Set G} (hs : IsFundamentalDomain Γ s μ)
    (hsm : MeasurableSet s) (hζ : Measurable ζ) (hcent : ∀ a g, ζ a * g = g * ζ a)
    (t : Set A) {S : Set G} (hS : MeasurableSet S)
    (hSΓ : ∀ (γ : Γ) (x : G), (γ : G) * x ∈ S ↔ x ∈ S)
    (hfib : ∀ g : G, ν (t ∩ {a | (ζ a)⁻¹ * g ∈ S}) = 1)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfΓ : ∀ (γ : Γ) (x : G), f ((γ : G) * x) = f x) :
    ∫⁻ g in s, f g ∂μ = ∫⁻ g in s ∩ S, ∫⁻ a in t, f (ζ a * g) ∂ν ∂μ := by
  have hk : ∀ a, ∫⁻ g in s, S.indicator 1 g * f (ζ a * g) ∂μ =
      ∫⁻ g in s, S.indicator 1 ((ζ a)⁻¹ * g) * f g ∂μ := by
    intro a
    have hb := hcent a
    have hb' := inv_mul_comm_of_central hb
    have h := setLIntegral_comp_mul_left Γ μ hs hsm (ζ a) hb
      (fun y => S.indicator 1 ((ζ a)⁻¹ * y) * f y) fun γ x => by
        show S.indicator 1 ((ζ a)⁻¹ * ((γ : G) * x)) * f ((γ : G) * x) =
          S.indicator 1 ((ζ a)⁻¹ * x) * f x
        rw [hfΓ, ← mul_assoc, hb', mul_assoc]
        by_cases hx : (ζ a)⁻¹ * x ∈ S
        · simp only [indicator_of_mem hx, indicator_of_mem ((hSΓ γ _).2 hx), Pi.one_apply]
        · simp only [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hSΓ γ _).1 h))]
    simpa only [inv_mul_cancel_left] using h
  have hm1 : Measurable (Function.uncurry fun (g : G) (a : A) =>
      S.indicator 1 g * f (ζ a * g)) :=
    ((measurable_one.indicator hS).comp measurable_fst).mul
      (hf.comp ((hζ.comp measurable_snd).mul measurable_fst))
  have hm2 : Measurable (Function.uncurry fun (g : G) (a : A) =>
      S.indicator 1 ((ζ a)⁻¹ * g) * f g) :=
    ((measurable_one.indicator hS).comp ((hζ.comp measurable_snd).inv.mul measurable_fst)).mul
      (hf.comp measurable_fst)
  calc ∫⁻ g in s, f g ∂μ
      = ∫⁻ g in s, ∫⁻ a in t, S.indicator 1 ((ζ a)⁻¹ * g) * f g ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        have hmS : MeasurableSet {a | (ζ a)⁻¹ * g ∈ S} :=
          hS.preimage ((hζ.inv).mul_const g)
        have hfun : (fun a => S.indicator 1 ((ζ a)⁻¹ * g)) =
            {a | (ζ a)⁻¹ * g ∈ S}.indicator (1 : A → ℝ≥0∞) := by
          funext a
          by_cases ha : (ζ a)⁻¹ * g ∈ S
          · simp only [indicator_of_mem ha,
              indicator_of_mem (show a ∈ {a | (ζ a)⁻¹ * g ∈ S} from ha), Pi.one_apply]
          · simp only [indicator_of_notMem ha,
              indicator_of_notMem (show a ∉ {a | (ζ a)⁻¹ * g ∈ S} from ha)]
        rw [lintegral_mul_const _ (by rw [hfun]; exact measurable_one.indicator hmS), hfun,
          lintegral_indicator_one hmS, Measure.restrict_apply hmS, inter_comm, hfib, one_mul]
    _ = ∫⁻ a in t, ∫⁻ g in s, S.indicator 1 ((ζ a)⁻¹ * g) * f g ∂μ ∂ν :=
        lintegral_lintegral_swap hm2.aemeasurable
    _ = ∫⁻ a in t, ∫⁻ g in s, S.indicator 1 g * f (ζ a * g) ∂μ ∂ν :=
        lintegral_congr fun a => (hk a).symm
    _ = ∫⁻ g in s, ∫⁻ a in t, S.indicator 1 g * f (ζ a * g) ∂ν ∂μ :=
        (lintegral_lintegral_swap hm1.aemeasurable).symm
    _ = ∫⁻ g in s ∩ S, ∫⁻ a in t, f (ζ a * g) ∂ν ∂μ := by
        rw [inter_comm, ← Measure.restrict_restrict hS, ← lintegral_indicator hS]
        refine lintegral_congr fun g => ?_
        by_cases hg : g ∈ S
        · simp only [indicator_of_mem hg, Pi.one_apply, one_mul]
        · simp only [indicator_of_notMem hg, zero_mul, lintegral_zero]

/-- **The quotient measure as the image of a product.** Under the hypotheses of
`lintegral_eq_lintegral_fibration`, the quotient measure of `s` is the image of
`μ|_(s ∩ S) ⊗ ν|_t` under `(g, a) ↦ Γ ζ(a) g`. -/
theorem quotientMeasure_eq_map_fibration {s : Set G} (hs : IsFundamentalDomain Γ s μ)
    (hsm : MeasurableSet s) (hζ : Measurable ζ) (hcent : ∀ a g, ζ a * g = g * ζ a)
    (t : Set A) {S : Set G} (hS : MeasurableSet S)
    (hSΓ : ∀ (γ : Γ) (x : G), (γ : G) * x ∈ S ↔ x ∈ S)
    (hfib : ∀ g : G, ν (t ∩ {a | (ζ a)⁻¹ * g ∈ S}) = 1) :
    LeftCosetSpace.quotientMeasure Γ μ s =
      Measure.map (fun p : G × A => LeftCosetSpace.mk Γ (ζ p.2 * p.1))
        ((μ.restrict (s ∩ S)).prod (ν.restrict t)) := by
  have hΨ : Measurable (fun p : G × A => LeftCosetSpace.mk Γ (ζ p.2 * p.1)) :=
    (LeftCosetSpace.measurable_mk Γ).comp ((hζ.comp measurable_snd).mul measurable_fst)
  ext B hB
  have hBm : MeasurableSet (LeftCosetSpace.mk Γ ⁻¹' B) := LeftCosetSpace.measurable_mk Γ hB
  rw [LeftCosetSpace.quotientMeasure_apply Γ μ s hB, Measure.map_apply hΨ hB,
    Measure.prod_apply (hΨ hB)]
  have h := lintegral_eq_lintegral_fibration Γ μ ν ζ hs hsm hζ hcent t hS hSΓ hfib
    ((LeftCosetSpace.mk Γ ⁻¹' B).indicator 1) (measurable_one.indicator hBm) fun γ x => by
      have hiff : (γ : G) * x ∈ LeftCosetSpace.mk Γ ⁻¹' B ↔ x ∈ LeftCosetSpace.mk Γ ⁻¹' B := by
        simp only [mem_preimage, LeftCosetSpace.mk_subgroup_mul]
      by_cases hx : x ∈ LeftCosetSpace.mk Γ ⁻¹' B
      · simp only [indicator_of_mem hx, indicator_of_mem (hiff.2 hx), Pi.one_apply]
      · simp only [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hiff.1 h))]
  rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm] at h
  rw [h]
  refine lintegral_congr fun g => ?_
  have hmg : MeasurableSet (Prod.mk g ⁻¹' ((fun p : G × A =>
      LeftCosetSpace.mk Γ (ζ p.2 * p.1)) ⁻¹' B)) := measurable_prodMk_left (hΨ hB)
  rw [← lintegral_indicator_one hmg]
  exact lintegral_congr fun a => rfl

end Fibration

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
