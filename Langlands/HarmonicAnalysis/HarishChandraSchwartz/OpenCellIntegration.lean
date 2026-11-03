import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod

/-! # The open-cell integration formula and `γ(P)` (Waldspurger I.1 (2), (3))

Waldspurger 2003, I.1 (2), second formula: for `f ∈ C_c^∞(G)`,
`∫_G f(g) dg = γ(P)⁻¹ ∫_{U × M × Ū} f(u m ū) δ_P(m)⁻¹ dū dm du`, with
`γ(P) = ∫_Ū δ_P(m_P(ū)) dū`. Writing `d_l p = δ_P(m)⁻¹ du dm` for the left Haar measure of
`P = M U`, this says `∫_G f = γ(P)⁻¹ ∫_P ∫_Ū f(p ū) dū d_l p`. This module proves the formula
for abstract data: a unimodular Haar measure on `G`, closed subgroups `P` and `V = Ū` with
Haar measures, and the open-cell map `(p, v) ↦ p v⁻¹`, assumed to be an open embedding with
conull image. The pull-back of the Haar measure of `G` is a left invariant measure on the
group `P × V`, hence a multiple of the product Haar measure; the constant is identified by
integrating the indicator of a subgroup `K` with `G = P K`, which gives
`γ = ∫_V δ(p(v)) dv` for the `P`-component `p(v)` of `v⁻¹`.
-/

noncomputable section

open scoped ENNReal NNReal Pointwise
open MeasureTheory Measure Topology

namespace Langlands.HarishChandraSchwartz

section Cell

variable {G : Type*} [Group G] {P V : Subgroup G}

/-- The open-cell coordinates `(p, v) ↦ p v⁻¹` on `P × V`. -/
def openCellMap (x : P × V) : G :=
  (x.1 : G) * (x.2 : G)⁻¹

theorem openCellMap_mul (q x : P × V) :
    openCellMap (q * x) = (q.1 : G) * openCellMap x * (q.2 : G)⁻¹ := by
  simp only [openCellMap, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
  group

/-- Translating in `P × V` corresponds to `g ↦ p g v⁻¹` on the image of the open-cell map. -/
theorem image_preimage_mul_openCellMap (q : P × V) (S : Set (P × V)) :
    openCellMap '' ((q * ·) ⁻¹' S) =
      (fun g => (q.1 : G) * g * (q.2 : G)⁻¹) ⁻¹' (openCellMap '' S) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨q * x, hx, openCellMap_mul q x⟩
  · rintro ⟨y, hy, hyg⟩
    refine ⟨q⁻¹ * y, by simpa using hy, ?_⟩
    rw [openCellMap_mul, hyg]
    simp only [Prod.fst_inv, Prod.snd_inv, InvMemClass.coe_inv, inv_inv]
    group

end Cell

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {P V : Subgroup G} [LocallyCompactSpace P] [LocallyCompactSpace V]
  [SecondCountableTopology P] [SecondCountableTopology V]
  (μ : Measure G) [IsHaarMeasure μ] [μ.IsMulRightInvariant]
  (μP : Measure P) [IsHaarMeasure μP] (μV : Measure V) [IsHaarMeasure μV]

/-- The pull-back of `μ` by the open-cell map is a multiple `c` of the product Haar measure:
for measurable `F ≥ 0`, `∫_{P V} F dμ = c ∫_P ∫_V F(p v⁻¹) dμ_V dμ_P`, with `c > 0`. Here `μ` is
left and right invariant (Waldspurger's `G` is unimodular), and `(p, v) ↦ p v⁻¹` is an open
embedding of `P × V` into `G`. -/
theorem exists_lintegral_range_openCellMap
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V))) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g in Set.range (openCellMap (P := P) (V := V)), F g ∂μ =
        c * ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP := by
  have hme := hι.measurableEmbedding
  set ν : Measure (P × V) := Measure.comap openCellMap μ with hν
  have hνinv : ν.IsMulLeftInvariant := ⟨fun q => by
    ext S hS
    rw [map_apply (measurable_const_mul q) hS, hme.comap_apply, hme.comap_apply,
      image_preimage_mul_openCellMap,
      show (fun g => (q.1 : G) * g * (q.2 : G)⁻¹) ⁻¹' (openCellMap '' S) =
        (fun g => (q.1 : G) * g) ⁻¹' ((fun g => g * (q.2 : G)⁻¹) ⁻¹' (openCellMap '' S)) from rfl,
      measure_preimage_mul, measure_preimage_mul_right]⟩
  have hνfin : IsFiniteMeasureOnCompacts ν := ⟨fun S hS => by
    rw [hme.comap_apply]
    exact (hS.image hι.continuous).measure_lt_top⟩
  have heq := isMulLeftInvariant_eq_smul ν (μP.prod μV)
  set c := haarScalarFactor ν (μP.prod μV)
  have hint : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g in Set.range (openCellMap (P := P) (V := V)), F g ∂μ =
        c * ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP := by
    intro F hF
    rw [← hme.map_comap μ, hme.lintegral_map, ← hν, heq, lintegral_smul_measure,
      lintegral_prod (fun x => F (openCellMap x)) (hF.comp hι.continuous.measurable).aemeasurable,
      ENNReal.smul_def, smul_eq_mul]
    rfl
  refine ⟨c, ?_, hint⟩
  rw [pos_iff_ne_zero]
  intro hc
  have h1 := hint (fun _ => 1) measurable_const
  rw [hc, ENNReal.coe_zero, zero_mul, lintegral_const, one_mul,
    Measure.restrict_apply_univ] at h1
  exact (hι.isOpen_range.measure_ne_zero μ ⟨_, Set.mem_range_self (1 : P × V)⟩) h1

/-- The open-cell formula on all of `G`, when the image of the open-cell map is conull. -/
theorem exists_lintegral_openCellMap (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g, F g ∂μ = c * ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP := by
  obtain ⟨c, hc, h⟩ := exists_lintegral_range_openCellMap μ μP μV hι
  refine ⟨c, hc, fun F hF => ?_⟩
  rw [← h F hF, Measure.restrict_eq_self_of_ae_mem]
  exact measure_eq_zero_iff_ae_notMem.mp hnull |>.mono fun _ hx => not_not.mp hx

/-- Waldspurger's constant `γ`: `∫_V μ_P{p | p v⁻¹ ∈ K} dμ_V(v)`, written as a double integral of
the indicator of `K`. -/
def openCellConstant (μP : Measure P) (μV : Measure V) (K : Subgroup G) : ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ p, (K : Set G).indicator 1 ((p : G) * (v : G)⁻¹) ∂μP ∂μV

omit [IsHaarMeasure μ] [μ.IsMulRightInvariant] in
/-- The constant of the open-cell formula: integrating the indicator of a measurable subgroup
`K` gives `μ(K) = c γ`. -/
theorem measure_eq_mul_openCellConstant {c : ℝ≥0}
    (hc : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g, F g ∂μ = c * ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G)) :
    μ K = c * openCellConstant μP μV K := by
  have hm : Measurable ((K : Set G).indicator (1 : G → ℝ≥0∞)) :=
    measurable_one.indicator hK
  have h := hc _ hm
  rw [lintegral_indicator_one hK] at h
  rw [h, openCellConstant, lintegral_lintegral_swap]
  exact (hm.comp ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd).inv).measurable).aemeasurable

/-- Waldspurger I.1 (2), second formula, for abstract data: if the image of the open-cell map
is conull and `K` is a measurable subgroup with `0 < μ(K) < ∞`, then `0 < γ < ∞` and
`∫_G F dμ = μ(K) γ⁻¹ ∫_P ∫_V F(p v⁻¹) dμ_V dμ_P` for measurable `F ≥ 0`, where
`γ = openCellConstant μP μV K`. With Waldspurger's normalization `μ(K) = 1`. -/
theorem lintegral_eq_openCellConstant_inv_mul
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0) {K : Subgroup G}
    (hK : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤) :
    openCellConstant μP μV K ≠ 0 ∧ openCellConstant μP μV K ≠ ⊤ ∧
      ∀ F : G → ℝ≥0∞, Measurable F →
        ∫⁻ g, F g ∂μ = μ K * (openCellConstant μP μV K)⁻¹ *
          ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP := by
  obtain ⟨c, hc0, hc⟩ := exists_lintegral_openCellMap μ μP μV hι hnull
  have hKc := measure_eq_mul_openCellConstant μ μP μV hc hK
  have hc0' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  have hγ0 : openCellConstant μP μV K ≠ 0 := by
    intro h; rw [h, mul_zero] at hKc; exact hK0 hKc
  have hγtop : openCellConstant μP μV K ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top hc0'] at hKc; exact hKtop hKc
  refine ⟨hγ0, hγtop, fun F hF => ?_⟩
  rw [hc F hF, hKc, mul_assoc (c : ℝ≥0∞), ENNReal.mul_inv_cancel hγ0 hγtop, mul_one]

end Haar

section Constant

variable {G : Type*} [Group G] [MeasurableSpace G] {P V : Subgroup G} [MeasurableMul P]
  (μP : Measure P) (μV : Measure V)

/-- The value of `γ`: suppose `μ_P((· p₀)⁻¹ S) = d(p₀) μ_P(S)` for measurable `S` (right
translation by `p₀` scales `μ_P` by `d(p₀)`; for Waldspurger `d(p₀) = δ_P(m_P(p₀))`),
`μ_P(P ∩ K) = 1`, `P ∩ K` is measurable in `P`, and `ℓ : V → P` picks the `P`-component of
`v⁻¹` in `G = P K`, that is `ℓ(v)⁻¹ v⁻¹ ∈ K`. Then `γ = ∫_V d(ℓ(v)) dμ_V`. For Waldspurger's data,
with `ū = v⁻¹` and `dū` inversion invariant, this is `γ(P) = ∫_Ū δ_P(m_P(ū)) dū`. -/
theorem openCellConstant_eq_lintegral {K : Subgroup G} {d : P → ℝ≥0∞}
    (hd : ∀ p₀ : P, ∀ S : Set P, MeasurableSet S → μP ((fun p => p * p₀) ⁻¹' S) = d p₀ * μP S)
    (hPK : MeasurableSet {p : P | (p : G) ∈ K}) (hPK1 : μP {p : P | (p : G) ∈ K} = 1)
    (ℓ : V → P) (hℓ : ∀ v : V, ((ℓ v : G))⁻¹ * (v : G)⁻¹ ∈ K) :
    openCellConstant μP μV K = ∫⁻ v, d (ℓ v) ∂μV := by
  refine lintegral_congr fun v => ?_
  have hset : ∀ p : P, (K : Set G).indicator (1 : G → ℝ≥0∞) ((p : G) * (v : G)⁻¹) =
      ((fun p => p * ℓ v) ⁻¹' {p : P | (p : G) ∈ K}).indicator 1 p := by
    intro p
    have hiff : (p : G) * (v : G)⁻¹ ∈ K ↔ ((p * ℓ v : P) : G) ∈ K := by
      have hk := hℓ v
      have e : (p : G) * (v : G)⁻¹ = ((p * ℓ v : P) : G) * (((ℓ v : G))⁻¹ * (v : G)⁻¹) := by
        simp only [Subgroup.coe_mul]; group
      rw [e]
      exact ⟨fun h => by simpa using K.mul_mem h (K.inv_mem hk),
        fun h => K.mul_mem h hk⟩
    by_cases h : (p : G) * (v : G)⁻¹ ∈ K
    · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from h),
        Set.indicator_of_mem (show p ∈ (fun p => p * ℓ v) ⁻¹' {p : P | (p : G) ∈ K} from
          hiff.mp h)]
      rfl
    · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from h),
        Set.indicator_of_notMem (show p ∉ (fun p => p * ℓ v) ⁻¹' {p : P | (p : G) ∈ K} from
          fun h' => h (hiff.mpr h'))]
  simp_rw [hset]
  rw [lintegral_indicator_one ((measurable_mul_const (ℓ v)) hPK), hd _ _ hPK, hPK1, mul_one]

end Constant

end Langlands.HarishChandraSchwartz
