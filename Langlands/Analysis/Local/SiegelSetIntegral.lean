import Langlands.Analysis.Local.SiegelSetMeasure
import Mathlib.Analysis.PSeries

/-! # Weighted integrals over abstract Siegel-type sets

In a second-countable locally compact group `H`, let `Q = M ⋉ U` be a closed subgroup with a
continuous Levi projection and `K` a compact subgroup, and suppose that the measure of
right-`K`-saturated sets is bounded by a Haar measure of their trace on `Q`. For a continuous
homomorphism `a : A → H` into the centre of `M`, commuting with `K ∩ Q`, and finitely many
characters `λ_i` of `A` with compact box `1/2 ≤ λ_i ≤ 2` and `δ_U ∘ a ≤ ∏ λ_i ^ e_i`, the
integral of a measurable `f ≥ 0` over `ΩU ΩM a(C) K` is bounded by a constant times
`∑_κ Φ(κ)`, whenever `f(u m a(x) k) ≤ δ_U(a x) Φ(κ(x))` for the integer dyadic index
`κ(x) = (⌊log₂ λ_i(x)⌋)_i`. A separate lemma shows that polynomially decaying weights on `ℤ^ι`
are summable.
-/

noncomputable section

universe u v w

open MeasureTheory Topology
open scoped Pointwise NNReal ENNReal

namespace Langlands.SiegelSetMeasure

open Langlands.Aubert.General

section Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A set integral of a measurable function bounded by `c` on the set is at most `c` times the
(outer) measure of the set. The set need not be measurable. -/
theorem setLIntegral_le_mul_of_forall_le {s : Set α} {f : α → ℝ≥0∞} (hf : Measurable f)
    {c : ℝ≥0∞} (h : ∀ x ∈ s, f x ≤ c) : ∫⁻ x in s, f x ∂μ ≤ c * μ s := by
  have hae : ∀ᵐ x ∂(μ.restrict s), f x ≤ c := by
    rw [ae_iff]
    have hm : MeasurableSet {x | ¬ f x ≤ c} := by
      simp only [not_le]
      exact measurableSet_lt measurable_const hf
    rw [Measure.restrict_apply hm]
    have hempty : {x | ¬ f x ≤ c} ∩ s = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      exact fun hfx hx => hfx (h x hx)
    rw [hempty, measure_empty]
  calc ∫⁻ x in s, f x ∂μ ≤ ∫⁻ _ in s, c ∂μ := lintegral_mono_ae hae
    _ = c * μ s := setLIntegral_const s c

end Measure

section IntDyadic

/-- Two positive numbers with the same integer part of `log₂` have ratio in `[1/2, 2]`. -/
theorem div_mem_Icc_of_log_eq {r s : ℝ≥0} (hr : 0 < r) (hs : 0 < s)
    (h : Int.log 2 r = Int.log 2 s) : (2 : ℝ≥0)⁻¹ ≤ r / s ∧ r / s ≤ 2 := by
  have hr₁ : (2 : ℝ≥0) ^ Int.log 2 r ≤ r := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hr
    exact_mod_cast this
  have hr₂ : r < (2 : ℝ≥0) ^ (Int.log 2 r + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) r
    exact_mod_cast this
  have hs₁ : (2 : ℝ≥0) ^ Int.log 2 s ≤ s := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hs
    exact_mod_cast this
  have hs₂ : s < (2 : ℝ≥0) ^ (Int.log 2 s + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) s
    exact_mod_cast this
  rw [h] at hr₁ hr₂
  set k := Int.log 2 s
  rw [zpow_add_one₀ two_ne_zero] at hr₂ hs₂
  constructor
  · rw [le_div_iff₀ hs]
    calc (2 : ℝ≥0)⁻¹ * s ≤ (2 : ℝ≥0)⁻¹ * (2 ^ k * 2) := by gcongr
      _ = 2 ^ k := by rw [mul_comm, mul_assoc, mul_inv_cancel₀ two_ne_zero, mul_one]
      _ ≤ r := hr₁
  · rw [div_le_iff₀ hs]
    calc r ≤ 2 ^ k * 2 := hr₂.le
      _ = 2 * 2 ^ k := mul_comm _ _
      _ ≤ 2 * s := by gcongr

variable {A : Type v} [Group A] {ι : Type w} (lam : ι → A →* ℝ≥0ˣ)

/-- The integer dyadic multi-index `i ↦ ⌊log₂ λ_i(x)⌋` of a point. -/
def zIndex (x : A) : ι → ℤ := fun i => Int.log 2 (lam i x : ℝ≥0)

/-- Two points with the same integer dyadic index differ by a point of the dyadic box. -/
theorem inv_mul_mem_dyadicBox_of_zIndex_eq {x y : A} (h : zIndex lam x = zIndex lam y) :
    y⁻¹ * x ∈ dyadicBox lam := by
  intro i
  have hx : 0 < (lam i x : ℝ≥0) := pos_iff_ne_zero.mpr (Units.ne_zero _)
  have hy : 0 < (lam i y : ℝ≥0) := pos_iff_ne_zero.mpr (Units.ne_zero _)
  have hi := div_mem_Icc_of_log_eq hx hy (congrFun h i)
  have he : (lam i (y⁻¹ * x) : ℝ≥0) = (lam i x : ℝ≥0) / (lam i y : ℝ≥0) := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]
  rw [he]
  exact hi

end IntDyadic

section Group

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- **One piece of a Siegel set.** For `g ∈ M` central in `M` and commuting with `K ∩ Q`, the
measure of `ΩU ΩM (g B) K` is at most `c δ_U(g)⁻¹ μ_Q(W)`, where `W` is the trace on `Q` of the
compact set `ΩU ΩM B (K ∩ Q)`. -/
theorem measure_piece_le (μ : Measure H) {Q M U K : Subgroup H}
    (hQ : IsClosed (Q : Set H)) (hM : IsClosed (M : Set H)) (hU : IsClosed (U : Set H))
    (hK : IsCompact (K : Set H))
    (h : IsSemidirectDecomposition Q M U) (hp : Continuous h.projection)
    (μQ : Measure Q) [μQ.IsHaarMeasure] (c : ℝ≥0)
    (hc : ∀ S : Set H, MeasurableSet S → (∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) →
      μ S ≤ c * μQ (Subtype.val ⁻¹' S))
    {ΩU ΩM B : Set H} (hΩU : IsCompact ΩU) (hΩUU : ΩU ⊆ U)
    (hΩM : IsCompact ΩM) (hΩMM : ΩM ⊆ M) (hB : IsCompact B) (hBM : B ⊆ M)
    (g : H) (hgM : g ∈ M) (hgcent : ∀ m ∈ M, Commute g m)
    (hgK : ∀ k ∈ K, k ∈ Q → Commute k g) :
    μ (ΩU * ΩM * ((fun b => g * b) '' B) * K) ≤
      c * (((HaarModulus.closedNormalizerCharacter U hU
        ⟨g, h.levi_le_normalizer hgM⟩ : ℝ≥0) : ℝ≥0∞)⁻¹ *
          μQ (Subtype.val ⁻¹' (ΩU * ΩM * B * ((K : Set H) ∩ Q)))) := by
  let _ : LocallyCompactSpace Q := hQ.locallyCompactSpace
  let S : Set H := ΩU * ΩM * ((fun b => g * b) '' B) * K
  have hS_compact : IsCompact S :=
    ((hΩU.mul hΩM).mul (hB.image (continuous_const.mul continuous_id))).mul hK
  let W₀ : Set H := ΩU * ΩM * B * ((K : Set H) ∩ Q)
  let W : Set Q := Subtype.val ⁻¹' W₀
  let gQ : Q := ⟨g, h.levi_le hgM⟩
  have hpiece : Subtype.val ⁻¹' S ⊆ (fun q => q * gQ⁻¹) ⁻¹' W := by
    intro q hq
    obtain ⟨p, ⟨r, ⟨u, hu, m, hm, rfl⟩, y, ⟨b, hb, rfl⟩, rfl⟩, k, hk, hpk⟩ := hq
    beta_reduce at hpk
    have huQ : u ∈ Q := h.unipotent_le (hΩUU hu)
    have hmQ : m ∈ Q := h.levi_le (hΩMM hm)
    have hgQ : g ∈ Q := h.levi_le hgM
    have hbQ : b ∈ Q := h.levi_le (hBM hb)
    have hkQ : k ∈ Q := by
      have hk' : k = (u * m * (g * b))⁻¹ * (q : H) := by
        rw [← hpk]
        group
      rw [hk']
      exact Q.mul_mem (Q.inv_mem (Q.mul_mem (Q.mul_mem huQ hmQ) (Q.mul_mem hgQ hbQ))) q.2
    have e1 : g * b = b * g := (hgcent b (hBM hb)).eq
    have e2 : k * g = g * k := (hgK k hk hkQ).eq
    show ((q * gQ⁻¹ : Q) : H) ∈ W₀
    have hcalc : ((q * gQ⁻¹ : Q) : H) = u * m * b * k := by
      change (q : H) * g⁻¹ = _
      rw [← hpk, e1]
      calc u * m * (b * g) * k * g⁻¹ = u * m * b * (g * k) * g⁻¹ := by
            simp only [mul_assoc]
        _ = u * m * b * k := by
            rw [← e2]
            simp only [mul_assoc, mul_inv_cancel, mul_one]
    rw [hcalc]
    exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hu hm) hb) ⟨hk, hkQ⟩
  have hmod : HaarModulus.closedNormalizerCharacter Q hQ
      ⟨gQ, Subgroup.le_normalizer gQ.2⟩ =
      HaarModulus.closedNormalizerCharacter U hU ⟨g, h.levi_le_normalizer hgM⟩ := by
    have hgM' : g ∈ Subgroup.normalizer (M : Set H) := Subgroup.le_normalizer hgM
    rw [h.closedNormalizerCharacter_eq_mul hp hQ hM hU g _ hgM',
      closedNormalizerCharacter_eq_one_of_commute hM ⟨g, hgM'⟩ hgcent, one_mul]
  have hsat : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ S := by
    rintro s ⟨p, hp', k', hk', rfl⟩ k hk
    rw [mul_assoc]
    exact Set.mul_mem_mul hp' (K.mul_mem hk' hk)
  calc μ S ≤ c * μQ (Subtype.val ⁻¹' S) := hc _ hS_compact.isClosed.measurableSet hsat
    _ ≤ c * μQ ((fun q => q * gQ⁻¹) ⁻¹' W) := by gcongr
    _ = _ := by rw [measure_preimage_mul_right_inv hQ μQ W gQ, hmod]

/-- **Weighted chamber bound.** Let `a : A → H` be a continuous homomorphism into the centre
of `M` commuting with `K ∩ Q`, and let `λ_i` be finitely many characters of `A` with compact
dyadic box and `δ_U ∘ a ≤ ∏ λ_i ^ e_i`. There is a constant `D < ∞` such that for every
`C ⊆ A`, every measurable `f ≥ 0` on `H` and every weight `Φ` on `ℤ^ι` with
`f(u m a(x) k) ≤ δ_U(a x) Φ(zIndex λ x)` for `x ∈ C`, `u ∈ ΩU`, `m ∈ ΩM`, `k ∈ K`, the
integral of `f` over `ΩU ΩM a(C) K` is at most `D ∑_κ Φ(κ)`. -/
theorem exists_lintegral_chamber_le (μ : Measure H) {Q M U K : Subgroup H}
    (hQ : IsClosed (Q : Set H)) (hM : IsClosed (M : Set H)) (hU : IsClosed (U : Set H))
    (hK : IsCompact (K : Set H))
    (h : IsSemidirectDecomposition Q M U) (hp : Continuous h.projection)
    (μQ : Measure Q) [μQ.IsHaarMeasure] (c : ℝ≥0)
    (hc : ∀ S : Set H, MeasurableSet S → (∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) →
      μ S ≤ c * μQ (Subtype.val ⁻¹' S))
    {ΩU ΩM : Set H} (hΩU : IsCompact ΩU) (hΩUU : ΩU ⊆ U)
    (hΩM : IsCompact ΩM) (hΩMM : ΩM ⊆ M)
    {A : Type v} [Group A] [TopologicalSpace A] (a : A →* H) (ha : Continuous a)
    (haM : ∀ x, a x ∈ M) (hacent : ∀ x, ∀ m ∈ M, Commute (a x) m)
    (haK : ∀ k ∈ K, k ∈ Q → ∀ x, Commute k (a x))
    {ι : Type w} [Fintype ι] (lam : ι → A →* ℝ≥0ˣ) (hbox : IsCompact (dyadicBox lam))
    (e : ι → ℕ)
    (hδ : ∀ x, (HaarModulus.closedNormalizerCharacter U hU
      ⟨a x, h.levi_le_normalizer (haM x)⟩ : ℝ≥0) ≤ ∏ i, (lam i x : ℝ≥0) ^ e i) :
    ∃ D : ℝ≥0∞, D ≠ ∞ ∧ ∀ (C : Set A) (f : H → ℝ≥0∞), Measurable f →
      ∀ Φ : (ι → ℤ) → ℝ≥0∞,
      (∀ x ∈ C, ∀ u ∈ ΩU, ∀ m ∈ ΩM, ∀ k ∈ K,
        f (u * m * a x * k) ≤ ((HaarModulus.closedNormalizerCharacter U hU
          ⟨a x, h.levi_le_normalizer (haM x)⟩ : ℝ≥0) : ℝ≥0∞) * Φ (zIndex lam x)) →
      ∫⁻ y in ΩU * ΩM * (a '' C) * K, f y ∂μ ≤ D * ∑' κ, Φ κ := by
  classical
  let _ : LocallyCompactSpace Q := hQ.locallyCompactSpace
  let B : Set H := a '' dyadicBox lam
  have hB : IsCompact B := hbox.image ha
  have hBM : B ⊆ M := by rintro _ ⟨x, -, rfl⟩; exact haM x
  let W₀ : Set H := ΩU * ΩM * B * ((K : Set H) ∩ Q)
  have hW₀ : IsCompact W₀ := ((hΩU.mul hΩM).mul hB).mul (hK.inter_right hQ)
  let W : Set Q := Subtype.val ⁻¹' W₀
  have hW : μQ W < ∞ :=
    (hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hW₀).measure_lt_top
  let R : ℝ≥0 := 2 ^ (∑ i, e i)
  -- the modulus `δ_U ∘ a`, as a function on `A`
  let δ : A → ℝ≥0 := fun x => (HaarModulus.closedNormalizerCharacter U hU
    ⟨a x, h.levi_le_normalizer (haM x)⟩ : ℝ≥0)
  have hδmul : ∀ x y, δ (x * y) = δ x * δ y := by
    intro x y
    have hxy : (⟨a (x * y), h.levi_le_normalizer (haM (x * y))⟩ :
        Subgroup.normalizer (U : Set H)) =
        ⟨a x, h.levi_le_normalizer (haM x)⟩ * ⟨a y, h.levi_le_normalizer (haM y)⟩ :=
      Subtype.ext (map_mul a x y)
    change ((HaarModulus.closedNormalizerCharacter U hU
      ⟨a (x * y), h.levi_le_normalizer (haM (x * y))⟩ : ℝ≥0ˣ) : ℝ≥0) = _
    rw [hxy, map_mul, Units.val_mul]
  have hδbox : ∀ b ∈ dyadicBox lam, δ b ≤ R := by
    intro b hb
    calc δ b ≤ ∏ i, (lam i b : ℝ≥0) ^ e i := hδ b
      _ ≤ ∏ i, (2 : ℝ≥0) ^ e i := Finset.prod_le_prod₀ (fun i _ => by positivity)
          (fun i _ => pow_le_pow_left₀ (by positivity) (hb i).2 _)
      _ = R := by rw [Finset.prod_pow_eq_pow_sum]
  have hδne : ∀ x, δ x ≠ 0 := fun x => Units.ne_zero _
  refine ⟨(R : ℝ≥0∞) * c * μQ W, ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
    ENNReal.coe_ne_top) hW.ne, ?_⟩
  intro C f hf Φ hbound
  -- the pieces, indexed by the integer dyadic indices that occur
  let J : Set (ι → ℤ) := zIndex lam '' C
  have hJ : ∀ κ : J, ∃ y ∈ C, zIndex lam y = κ := fun κ => κ.2
  choose y hy hyκ using hJ
  let P : J → Set H := fun κ =>
    ΩU * ΩM * (a '' (C ∩ zIndex lam ⁻¹' {(κ : ι → ℤ)})) * K
  have hcover : ΩU * ΩM * (a '' C) * K ⊆ ⋃ κ, P κ := by
    rintro _ ⟨p, ⟨q, ⟨u, hu, m, hm, rfl⟩, _, ⟨x, hx, rfl⟩, rfl⟩, k, hk, rfl⟩
    refine Set.mem_iUnion.mpr ⟨⟨zIndex lam x, x, hx, rfl⟩, ?_⟩
    exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hu hm) ⟨x, ⟨hx, rfl⟩, rfl⟩) hk
  have hPsub : ∀ κ, P κ ⊆ ΩU * ΩM * ((fun b => a (y κ) * b) '' B) * K := by
    rintro κ _ ⟨p, ⟨q, ⟨u, hu, m, hm, rfl⟩, _, ⟨x, ⟨hx, hxκ⟩, rfl⟩, rfl⟩, k, hk, rfl⟩
    have hxκ' : zIndex lam x = zIndex lam (y κ) := by rw [hyκ κ]; exact hxκ
    refine Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hu hm)
      ⟨a ((y κ)⁻¹ * x), ⟨_, inv_mul_mem_dyadicBox_of_zIndex_eq lam hxκ', rfl⟩, ?_⟩) hk
    beta_reduce
    rw [← map_mul, mul_inv_cancel_left]
  have hPf : ∀ κ, ∀ p ∈ P κ, f p ≤ ((R : ℝ≥0∞) * δ (y κ)) * Φ κ := by
    rintro κ _ ⟨p, ⟨q, ⟨u, hu, m, hm, rfl⟩, _, ⟨x, ⟨hx, hxκ⟩, rfl⟩, rfl⟩, k, hk, rfl⟩
    have hxκ' : zIndex lam x = (κ : ι → ℤ) := hxκ
    have hb : (y κ)⁻¹ * x ∈ dyadicBox lam :=
      inv_mul_mem_dyadicBox_of_zIndex_eq lam (hxκ'.trans (hyκ κ).symm)
    have hδx : δ x ≤ δ (y κ) * R := by
      calc δ x = δ (y κ * ((y κ)⁻¹ * x)) := by rw [mul_inv_cancel_left]
        _ = δ (y κ) * δ ((y κ)⁻¹ * x) := hδmul _ _
        _ ≤ δ (y κ) * R := by gcongr; exact hδbox _ hb
    calc f (u * m * a x * k) ≤ (δ x : ℝ≥0∞) * Φ (zIndex lam x) := hbound x hx u hu m hm k hk
      _ ≤ ((R : ℝ≥0∞) * δ (y κ)) * Φ κ := by
          rw [hxκ']
          gcongr
          rw [mul_comm]
          exact_mod_cast hδx
  have hPμ : ∀ κ, μ (P κ) ≤ c * (((δ (y κ) : ℝ≥0) : ℝ≥0∞)⁻¹ * μQ W) := fun κ =>
    (measure_mono (hPsub κ)).trans (measure_piece_le μ hQ hM hU hK h hp μQ c hc hΩU hΩUU
      hΩM hΩMM hB hBM (a (y κ)) (haM _) (hacent _) (fun k hk hkQ => haK k hk hkQ _))
  calc ∫⁻ x in ΩU * ΩM * (a '' C) * K, f x ∂μ ≤ ∫⁻ x in ⋃ κ, P κ, f x ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∑' κ, ∫⁻ x in P κ, f x ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' κ, ((R : ℝ≥0∞) * δ (y κ)) * Φ κ * μ (P κ) :=
        ENNReal.tsum_le_tsum fun κ => setLIntegral_le_mul_of_forall_le hf (hPf κ)
    _ ≤ ∑' κ, ((R : ℝ≥0∞) * δ (y κ)) * Φ κ * (c * (((δ (y κ) : ℝ≥0) : ℝ≥0∞)⁻¹ * μQ W)) :=
        ENNReal.tsum_le_tsum fun κ => by gcongr; exact hPμ κ
    _ = ∑' κ : J, (R : ℝ≥0∞) * c * μQ W * Φ κ := by
        refine tsum_congr fun κ => ?_
        have h1 : ((δ (y κ) : ℝ≥0) : ℝ≥0∞) * ((δ (y κ) : ℝ≥0) : ℝ≥0∞)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (hδne _)) ENNReal.coe_ne_top
        calc (R : ℝ≥0∞) * δ (y κ) * Φ κ * (c * ((δ (y κ) : ℝ≥0∞)⁻¹ * μQ W))
            = (R : ℝ≥0∞) * c * μQ W * Φ κ *
                (((δ (y κ) : ℝ≥0) : ℝ≥0∞) * ((δ (y κ) : ℝ≥0) : ℝ≥0∞)⁻¹) := by ring
          _ = _ := by rw [h1, mul_one]
    _ = (R : ℝ≥0∞) * c * μQ W * ∑' κ : J, Φ κ := ENNReal.tsum_mul_left
    _ ≤ (R : ℝ≥0∞) * c * μQ W * ∑' κ, Φ κ := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective Φ

end Group

section Sums

/-- A sum over `ι → β` of products is at most the product of the factor sums. -/
theorem tsum_pi_prod_le' {ι : Type w} {β : Type v} [Fintype ι] (f : ι → β → ℝ≥0∞) :
    ∑' m : ι → β, ∏ i, f i (m i) ≤ ∏ i, ∑' n, f i n := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ m ∈ s, ∏ i, f i (m i)
      ≤ ∑ m ∈ Fintype.piFinset (fun i => s.image (fun m => m i)), ∏ i, f i (m i) := by
        apply Finset.sum_le_sum_of_subset
        intro m hm
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_image_of_mem _ hm
    _ = ∏ i, ∑ n ∈ s.image (fun m => m i), f i n := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' n, f i n := Finset.prod_le_prod fun i _ => ENNReal.sum_le_tsum _

/-- The series `∑_{n ∈ ℤ} (1 + |n|)⁻²` converges. -/
theorem tsum_int_inv_one_add_abs_sq_ne_top :
    ∑' n : ℤ, ENNReal.ofReal (((1 + |(n : ℝ)|) ^ 2)⁻¹) ≠ ∞ := by
  have hsum : Summable (fun n : ℤ => ((1 + |(n : ℝ)|) ^ 2)⁻¹) := by
    have h1 : Summable (fun n : ℤ => |(n : ℝ)| ^ (-(2 : ℝ))) :=
      Real.summable_abs_int_rpow (by norm_num)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (h1.add (summable_of_ne_finset_zero (s := {0})
        (f := fun n : ℤ => if n = 0 then (1 : ℝ) else 0) (fun n hn => by
          simp only [Finset.mem_singleton] at hn
          simp [hn])))
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hpos : 0 < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
      have hle : ((1 + |(n : ℝ)|) ^ 2)⁻¹ ≤ |(n : ℝ)| ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hpos.le, Real.rpow_two]
        gcongr
        linarith
      simp only [hn, ite_false, add_zero]
      exact hle
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

/-- **Polynomially decaying weights on `ℤ^ι` are summable.** For `c > 0` and any `C₀`, the
weights `max(1, c ∑_i |κ_i| - C₀)^{-2|ι|}` have finite sum over `κ ∈ ℤ^ι`. -/
theorem tsum_decay_ne_top {ι : Type w} [Fintype ι] {c : ℝ} (hc : 0 < c) (C₀ : ℝ) :
    ∑' κ : ι → ℤ, ENNReal.ofReal
      ((max 1 (c * ∑ i, |(κ i : ℝ)| - C₀))⁻¹ ^ (2 * Fintype.card ι)) ≠ ∞ := by
  set n := Fintype.card ι
  set C₁ := max C₀ 0
  set K₀ : ℝ := min 1 c / (2 * (1 + C₁)) with hK₀
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  have hK₀pos : 0 < K₀ := div_pos (lt_min one_pos hc) (by positivity)
  -- `max 1 (c S - C₀) ≥ K₀ (1 + S)`
  have hlow : ∀ S : ℝ, 0 ≤ S → K₀ * (1 + S) ≤ max 1 (c * S - C₀) := by
    intro S hS
    set L := max 1 (c * S - C₀)
    have hL1 : 1 ≤ L := le_max_left _ _
    have hL2 : c * S - C₀ ≤ L := le_max_right _ _
    have hm1 : min 1 c ≤ 1 := min_le_left _ _
    have hm2 : min 1 c ≤ c := min_le_right _ _
    have hkey : min 1 c * (1 + S) ≤ 2 * (1 + C₁) * L := by
      have h1 : min 1 c * (1 + S) ≤ 1 + c * S := by nlinarith [min_le_left 1 c]
      have h2 : c * S ≤ L + C₁ := by
        have : C₀ ≤ C₁ := le_max_left _ _
        linarith
      nlinarith
    rw [hK₀, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  -- the comparison with a product
  have hbound : ∀ κ : ι → ℤ,
      ENNReal.ofReal ((max 1 (c * ∑ i, |(κ i : ℝ)| - C₀))⁻¹ ^ (2 * n)) ≤
        ENNReal.ofReal ((K₀⁻¹) ^ (2 * n)) *
          ∏ i, ENNReal.ofReal (((1 + |(κ i : ℝ)|) ^ 2)⁻¹) := by
    intro κ
    set S : ℝ := ∑ i, |(κ i : ℝ)|
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hSi : ∀ i, 1 + |(κ i : ℝ)| ≤ 1 + S := fun i => by
      have := Finset.single_le_sum (f := fun i => |(κ i : ℝ)|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ i)
      linarith
    have hprod : ∏ i, (1 + |(κ i : ℝ)|) ≤ (1 + S) ^ n := by
      calc ∏ i, (1 + |(κ i : ℝ)|) ≤ ∏ _i : ι, (1 + S) :=
            Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => hSi i
        _ = (1 + S) ^ n := by rw [Finset.prod_const, Finset.card_univ]
    have hL : K₀ * (1 + S) ≤ max 1 (c * S - C₀) := hlow S hS
    have hLpos : 0 < K₀ * (1 + S) := by positivity
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [Finset.prod_inv_distrib, Finset.prod_pow]
    calc (max 1 (c * S - C₀))⁻¹ ^ (2 * n) ≤ ((K₀ * (1 + S))⁻¹) ^ (2 * n) := by
          gcongr
      _ = (K₀⁻¹) ^ (2 * n) * (((1 + S) ^ n) ^ 2)⁻¹ := by
          rw [mul_inv, mul_pow, pow_mul, ← inv_pow, ← inv_pow]
          ring
      _ ≤ (K₀⁻¹) ^ (2 * n) * ((∏ i, (1 + |(κ i : ℝ)|)) ^ 2)⁻¹ := by
          gcongr
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  refine ne_top_of_le_ne_top ?_ (tsum_pi_prod_le' fun (_ : ι) (m : ℤ) =>
    ENNReal.ofReal (((1 + |(m : ℝ)|) ^ 2)⁻¹))
  exact ENNReal.prod_ne_top fun _ _ => tsum_int_inv_one_add_abs_sq_ne_top

end Sums

end Langlands.SiegelSetMeasure
