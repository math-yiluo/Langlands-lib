import Langlands.Representation.Aubert.General.SemidirectRestriction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Log

/-! # Finite Haar measure of abstract Siegel-type sets

In a second-countable locally compact group `H`, let `Q = M ⋉ U` be a closed
subgroup with a continuous Levi projection, and `K` a compact subgroup. If the
Haar measure of right-`K`-saturated sets is bounded by a Haar measure of their
trace on `Q`, then `ΩU ΩM C K` has finite measure whenever `C` is covered by
countably many translates `g n B` of a compact `B ⊆ M` by elements central in
`M` and commuting with `K ∩ Q`, and `∑ δ_U(g n)⁻¹ < ∞` for the Haar modulus `δ_U`
of conjugation on `U`. A dyadic covering of a chamber `t ≤ λ_i` supplies such a
cover when `δ_U ∘ a ≥ ∏ λ_i ^ e_i` with `e_i ≥ 1`.
-/

noncomputable section

universe u v w

open MeasureTheory Topology
open scoped Pointwise NNReal ENNReal

namespace Langlands.SiegelSetMeasure

open Langlands.Aubert.General

section Sums

/-- A sum over `ι → ℕ` of products is at most the product of the factor sums. -/
theorem tsum_pi_prod_le {ι : Type w} [Fintype ι] (f : ι → ℕ → ℝ≥0∞) :
    ∑' m : ι → ℕ, ∏ i, f i (m i) ≤ ∏ i, ∑' n, f i n := by
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

end Sums

section Dyadic

/-- The dyadic exponent `m` with `2 ^ m ≤ r < 2 ^ (m + 1)` for `r ≥ 1`. -/
def dyadicIndex (r : ℝ≥0) : ℕ := Nat.log 2 ⌊r⌋₊

theorem pow_dyadicIndex_le {r : ℝ≥0} (hr : 1 ≤ r) : (2 : ℝ≥0) ^ dyadicIndex r ≤ r := by
  have h := Int.zpow_log_le_self (b := 2) (r := r) (by norm_num) (zero_lt_one.trans_le hr)
  rw [Int.log_of_one_le_right 2 hr, zpow_natCast] at h
  exact_mod_cast h

theorem lt_pow_dyadicIndex_succ {r : ℝ≥0} (hr : 1 ≤ r) :
    r < (2 : ℝ≥0) ^ (dyadicIndex r + 1) := by
  have h := Int.lt_zpow_succ_log_self (b := 2) (R := ℝ≥0) (by norm_num) r
  rw [Int.log_of_one_le_right 2 hr, ← Nat.cast_succ, zpow_natCast] at h
  exact_mod_cast h

/-- Two numbers at least `t` with the same dyadic index of `· / t` have ratio in `[1/2, 2]`. -/
theorem div_mem_Icc_of_dyadicIndex_eq {t r s : ℝ≥0} (ht : t ≠ 0) (hr : t ≤ r) (hs : t ≤ s)
    (h : dyadicIndex (r / t) = dyadicIndex (s / t)) :
    (2 : ℝ≥0)⁻¹ ≤ r / s ∧ r / s ≤ 2 := by
  have htp : 0 < t := pos_iff_ne_zero.mpr ht
  have hr1 : 1 ≤ r / t := (one_le_div htp).mpr hr
  have hs1 : 1 ≤ s / t := (one_le_div htp).mpr hs
  have hrpos : 0 < r := htp.trans_le hr
  have hspos : 0 < s := htp.trans_le hs
  have hr₁ := pow_dyadicIndex_le hr1
  have hr₂ := lt_pow_dyadicIndex_succ hr1
  have hs₁ := pow_dyadicIndex_le hs1
  have hs₂ := lt_pow_dyadicIndex_succ hs1
  rw [h] at hr₁ hr₂
  set m := dyadicIndex (s / t)
  rw [pow_succ] at hr₂ hs₂
  have key : r / s = (r / t) / (s / t) := by
    rw [div_div_div_cancel_right₀ ht]
  rw [key]
  have hst : 0 < s / t := zero_lt_one.trans_le hs1
  constructor
  · rw [le_div_iff₀ hst]
    calc (2 : ℝ≥0)⁻¹ * (s / t) ≤ (2 : ℝ≥0)⁻¹ * (2 ^ m * 2) := by gcongr
      _ = 2 ^ m := by rw [mul_comm, mul_assoc, mul_inv_cancel₀ two_ne_zero, mul_one]
      _ ≤ r / t := hr₁
  · rw [div_le_iff₀ hst]
    calc r / t ≤ 2 ^ m * 2 := hr₂.le
      _ = 2 * 2 ^ m := mul_comm _ _
      _ ≤ 2 * (s / t) := by gcongr

end Dyadic

section Chamber

variable {A : Type v} [Group A] {ι : Type w} [Fintype ι] (lam : ι → A →* ℝ≥0ˣ)

/-- The weak chamber `t ≤ λ_i` for all `i`. -/
def chamber (t : ℝ≥0) : Set A := {x | ∀ i, t ≤ (lam i x : ℝ≥0)}

/-- The box `1/2 ≤ λ_i ≤ 2` for all `i`. -/
def dyadicBox : Set A := {x | ∀ i, (2 : ℝ≥0)⁻¹ ≤ (lam i x : ℝ≥0) ∧ (lam i x : ℝ≥0) ≤ 2}

/-- The dyadic multi-index of a point of the chamber. -/
def chamberIndex (t : ℝ≥0) (x : A) : ι → ℕ := fun i => dyadicIndex ((lam i x : ℝ≥0) / t)

omit [Fintype ι] in
theorem inv_mul_mem_dyadicBox {t : ℝ≥0} (ht : t ≠ 0) {x y : A}
    (hx : x ∈ chamber lam t) (hy : y ∈ chamber lam t)
    (h : chamberIndex lam t x = chamberIndex lam t y) :
    y⁻¹ * x ∈ dyadicBox lam := by
  intro i
  have hi := div_mem_Icc_of_dyadicIndex_eq ht (hx i) (hy i) (congrFun h i)
  have he : (lam i (y⁻¹ * x) : ℝ≥0) = (lam i x : ℝ≥0) / (lam i y : ℝ≥0) := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]
  rw [he]
  exact hi

/-- On the chamber the inverse of `∏ λ_i ^ e_i` is bounded by a product of
geometric terms in the dyadic index. -/
theorem inv_prod_pow_le {t : ℝ≥0} (ht : t ≠ 0) (e : ι → ℕ) (he : ∀ i, e i ≠ 0)
    {y : A} (hy : y ∈ chamber lam t) :
    ((∏ i, (lam i y : ℝ≥0) ^ e i : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      ∏ i, ((t : ℝ≥0∞) ^ e i)⁻¹ * 2⁻¹ ^ chamberIndex lam t y i := by
  have htp : 0 < t := pos_iff_ne_zero.mpr ht
  rw [ENNReal.ofNNReal_finsetProd, ENNReal.prod_inv_distrib]
  swap
  · intro i _ j _ _
    right
    exact ENNReal.coe_ne_top
  refine Finset.prod_le_prod fun i _ => ?_
  set m := chamberIndex lam t y i
  have hr1 : 1 ≤ (lam i y : ℝ≥0) / t := (one_le_div htp).mpr (hy i)
  have h1 : (2 : ℝ≥0) ^ m ≤ (lam i y : ℝ≥0) / t := pow_dyadicIndex_le hr1
  have h2 : t ^ e i * 2 ^ m ≤ (lam i y : ℝ≥0) ^ e i := by
    have h3 : t * 2 ^ m ≤ (lam i y : ℝ≥0) := by
      rw [mul_comm, ← le_div_iff₀ htp]
      exact h1
    calc t ^ e i * 2 ^ m ≤ t ^ e i * (2 ^ m) ^ e i :=
          mul_le_mul_of_nonneg_left
            (le_self_pow₀ (one_le_pow₀ (by norm_num : (1 : ℝ≥0) ≤ 2)) (he i)) (by positivity)
      _ = (t * 2 ^ m) ^ e i := (mul_pow _ _ _).symm
      _ ≤ (lam i y : ℝ≥0) ^ e i := by gcongr
  have h4 : ((t : ℝ≥0∞) ^ e i) * 2 ^ m ≤ (((lam i y : ℝ≥0) ^ e i : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast h2
  calc ((((lam i y : ℝ≥0) ^ e i : ℝ≥0) : ℝ≥0∞))⁻¹ ≤ ((t : ℝ≥0∞) ^ e i * 2 ^ m)⁻¹ :=
        ENNReal.inv_le_inv' h4
    _ = ((t : ℝ≥0∞) ^ e i)⁻¹ * 2⁻¹ ^ m := by
        rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
        simp only [ENNReal.inv_pow]

/-- The geometric bound summed over all multi-indices is finite. -/
theorem tsum_prod_geometric_ne_top {t : ℝ≥0} (ht : t ≠ 0) (e : ι → ℕ) :
    ∑' m : ι → ℕ, ∏ i, ((t : ℝ≥0∞) ^ e i)⁻¹ * 2⁻¹ ^ m i ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (tsum_pi_prod_le fun i n => ((t : ℝ≥0∞) ^ e i)⁻¹ * 2⁻¹ ^ n)
  refine ENNReal.prod_ne_top fun i _ => ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
  refine ENNReal.mul_ne_top ?_ (by simp)
  rw [ENNReal.inv_ne_top]
  exact pow_ne_zero _ (ENNReal.coe_ne_zero.mpr ht)

end Chamber

section Group

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- `mulEquivHaarChar` does not depend on the choice of Borel σ-algebra instance. -/
theorem mulEquivHaarChar_congr {G : Type w} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] {m₁ m₂ : MeasurableSpace G}
    (h₁ : @BorelSpace G _ m₁) (h₂ : @BorelSpace G _ m₂) (φ : G ≃ₜ* G) :
    @mulEquivHaarChar G _ _ m₁ h₁ _ _ φ = @mulEquivHaarChar G _ _ m₂ h₂ _ _ φ := by
  obtain rfl : m₁ = m₂ := h₁.measurable_eq.trans h₂.measurable_eq.symm
  rfl

omit [T2Space H] [SecondCountableTopology H] in
/-- The closed normalizer character, read with the subtype σ-algebra. -/
theorem coe_closedNormalizerCharacter {U : Subgroup H} (hU : IsClosed (U : Set H))
    (g : Subgroup.normalizer (U : Set H)) :
    letI : LocallyCompactSpace U := hU.locallyCompactSpace
    (HaarModulus.closedNormalizerCharacter U hU g : ℝ≥0) =
      mulEquivHaarChar (HaarModulus.normalizerConj U g) := by
  let _ : LocallyCompactSpace U := hU.locallyCompactSpace
  exact mulEquivHaarChar_congr (@BorelSpace.mk U _ (borel U) rfl) inferInstance _

omit [T2Space H] [SecondCountableTopology H] in
/-- The closed normalizer character of an element central in a closed subgroup is one. -/
theorem closedNormalizerCharacter_eq_one_of_commute {M : Subgroup H}
    (hM : IsClosed (M : Set H)) (g : Subgroup.normalizer (M : Set H))
    (hg : ∀ m ∈ M, Commute (g : H) m) :
    HaarModulus.closedNormalizerCharacter M hM g = 1 := by
  let _ : LocallyCompactSpace M := hM.locallyCompactSpace
  apply Units.ext
  rw [coe_closedNormalizerCharacter hM g]
  have : HaarModulus.normalizerConj M g = ContinuousMulEquiv.refl M := by
    ext m
    simp [(hg m m.2).eq]
  rw [this, mulEquivHaarChar_refl]
  rfl

omit [T2Space H] in
/-- Right translation by `g` in a closed subgroup scales Haar measure by the
inverse of the Haar modulus of conjugation by `g`. -/
theorem measure_preimage_mul_right_inv {Q : Subgroup H} (hQ : IsClosed (Q : Set H))
    (μQ : Measure Q) [μQ.IsHaarMeasure] (W : Set Q) (g : Q) :
    μQ ((fun q => q * g⁻¹) ⁻¹' W) =
      ((HaarModulus.closedNormalizerCharacter Q hQ
        ⟨g, Subgroup.le_normalizer g.2⟩ : ℝ≥0) : ℝ≥0∞)⁻¹ * μQ W := by
  let _ : LocallyCompactSpace Q := hQ.locallyCompactSpace
  have _ : SecondCountableTopology Q := inferInstanceAs (SecondCountableTopology (Q : Set H))
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts Q) := inferInstance
  have _ : μQ.Regular := Measure.regular_of_isMulLeftInvariant K₀.isCompact
    K₀.interior_nonempty K₀.isCompact.measure_lt_top.ne
  set φ := HaarModulus.normalizerConj Q ⟨g, Subgroup.le_normalizer g.2⟩
  have hset : (fun q => q * g⁻¹) ⁻¹' W = (fun q => g⁻¹ * q) ⁻¹' (φ ⁻¹' W) := by
    ext q
    simp only [Set.mem_preimage]
    congr! 1
    apply Subtype.ext
    simp [φ, mul_assoc]
  rw [hset, measure_preimage_mul, coe_closedNormalizerCharacter hQ]
  have key := mulEquivHaarChar_smul_preimage μQ (X := W) φ
  rw [← key, ENNReal.smul_def, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simpa using (mulEquivHaarChar_pos φ).ne') ENNReal.coe_ne_top,
    one_mul]

/-- **Abstract Siegel-set bound.** Countably many translates `g n B` of a compact
`B ⊆ M`, by elements central in `M` and commuting with `K ∩ Q`, cover `C`; the
Haar measure of right-`K`-saturated measurable sets is bounded by `c` times the
Haar measure of their trace on `Q`; and `∑ δ_U(g n)⁻¹ < ∞`. Then `ΩU ΩM C K` has
finite Haar measure. -/
theorem measure_mul_mul_mul_lt_top (μ : Measure H) {Q M U K : Subgroup H}
    (hQ : IsClosed (Q : Set H)) (hM : IsClosed (M : Set H)) (hU : IsClosed (U : Set H))
    (hK : IsCompact (K : Set H))
    (h : IsSemidirectDecomposition Q M U) (hp : Continuous h.projection)
    (μQ : Measure Q) [μQ.IsHaarMeasure] (c : ℝ≥0)
    (hc : ∀ S : Set H, MeasurableSet S → (∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) →
      μ S ≤ c * μQ (Subtype.val ⁻¹' S))
    {ΩU ΩM B C : Set H} (hΩU : IsCompact ΩU) (hΩUU : ΩU ⊆ U)
    (hΩM : IsCompact ΩM) (hΩMM : ΩM ⊆ M) (hB : IsCompact B) (hBM : B ⊆ M)
    {J : Type*} [Countable J] (g : J → H) (hgM : ∀ n, g n ∈ M)
    (hgcent : ∀ n, ∀ m ∈ M, Commute (g n) m)
    (hgK : ∀ n, ∀ k ∈ K, k ∈ Q → Commute k (g n))
    (hcover : ∀ x ∈ C, ∃ n, ∃ b ∈ B, x = g n * b)
    (hsum : ∑' n, ((HaarModulus.closedNormalizerCharacter U hU
      ⟨g n, h.levi_le_normalizer (hgM n)⟩ : ℝ≥0) : ℝ≥0∞)⁻¹ ≠ ∞) :
    μ (ΩU * ΩM * C * K) < ∞ := by
  let _ : LocallyCompactSpace Q := hQ.locallyCompactSpace
  -- the pieces of the cover
  let S : J → Set H := fun n => ΩU * ΩM * ((fun b => g n * b) '' B) * K
  have hS_compact : ∀ n, IsCompact (S n) := fun n =>
    ((hΩU.mul hΩM).mul (hB.image (continuous_const.mul continuous_id))).mul hK
  have hsub : ΩU * ΩM * C * K ⊆ ⋃ n, S n := by
    rintro x ⟨p, ⟨q, ⟨u, hu, m, hm, rfl⟩, y, hy, rfl⟩, k, hk, rfl⟩
    obtain ⟨n, b, hb, rfl⟩ := hcover y hy
    exact Set.mem_iUnion.mpr ⟨n, Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hu hm)
      ⟨b, hb, rfl⟩) hk⟩
  -- the compact set in `Q` controlling every piece
  let W₀ : Set H := ΩU * ΩM * B * ((K : Set H) ∩ Q)
  have hW₀ : IsCompact W₀ := ((hΩU.mul hΩM).mul hB).mul (hK.inter_right hQ)
  let W : Set Q := Subtype.val ⁻¹' W₀
  have hW : μQ W < ∞ :=
    (hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hW₀).measure_lt_top
  let gQ : J → Q := fun n => ⟨g n, h.levi_le (hgM n)⟩
  have hpiece : ∀ n, Subtype.val ⁻¹' S n ⊆ (fun q => q * (gQ n)⁻¹) ⁻¹' W := by
    intro n q hq
    obtain ⟨p, ⟨r, ⟨u, hu, m, hm, rfl⟩, y, ⟨b, hb, rfl⟩, rfl⟩, k, hk, hpk⟩ := hq
    beta_reduce at hpk
    have huQ : u ∈ Q := h.unipotent_le (hΩUU hu)
    have hmQ : m ∈ Q := h.levi_le (hΩMM hm)
    have hgQ : g n ∈ Q := h.levi_le (hgM n)
    have hbQ : b ∈ Q := h.levi_le (hBM hb)
    have hkQ : k ∈ Q := by
      have hk' : k = (u * m * (g n * b))⁻¹ * (q : H) := by
        rw [← hpk]
        group
      rw [hk']
      exact Q.mul_mem (Q.inv_mem (Q.mul_mem (Q.mul_mem huQ hmQ) (Q.mul_mem hgQ hbQ))) q.2
    have e1 : g n * b = b * g n := (hgcent n b (hBM hb)).eq
    have e2 : k * g n = g n * k := (hgK n k hk hkQ).eq
    show ((q * (gQ n)⁻¹ : Q) : H) ∈ W₀
    have hcalc : ((q * (gQ n)⁻¹ : Q) : H) = u * m * b * k := by
      change (q : H) * (g n)⁻¹ = _
      rw [← hpk, e1]
      calc u * m * (b * g n) * k * (g n)⁻¹ = u * m * b * (g n * k) * (g n)⁻¹ := by
            simp only [mul_assoc]
        _ = u * m * b * k := by
            rw [← e2]
            simp only [mul_assoc, mul_inv_cancel, mul_one]
    rw [hcalc]
    exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hu hm) hb) ⟨hk, hkQ⟩
  -- the modulus of `Q` at `g n` is that of `U`
  have hmod : ∀ n, HaarModulus.closedNormalizerCharacter Q hQ
      ⟨gQ n, Subgroup.le_normalizer (gQ n).2⟩ =
      HaarModulus.closedNormalizerCharacter U hU ⟨g n, h.levi_le_normalizer (hgM n)⟩ := by
    intro n
    have hgM' : g n ∈ Subgroup.normalizer (M : Set H) := Subgroup.le_normalizer (hgM n)
    rw [h.closedNormalizerCharacter_eq_mul hp hQ hM hU (g n) _ hgM',
      closedNormalizerCharacter_eq_one_of_commute hM ⟨g n, hgM'⟩ (hgcent n), one_mul]
  have hbound : ∀ n, μ (S n) ≤ c * (((HaarModulus.closedNormalizerCharacter U hU
      ⟨g n, h.levi_le_normalizer (hgM n)⟩ : ℝ≥0) : ℝ≥0∞)⁻¹ * μQ W) := by
    intro n
    have hsat : ∀ s ∈ S n, ∀ k ∈ K, s * k ∈ S n := by
      rintro s ⟨p, hp', k', hk', rfl⟩ k hk
      rw [mul_assoc]
      exact Set.mul_mem_mul hp' (K.mul_mem hk' hk)
    calc μ (S n) ≤ c * μQ (Subtype.val ⁻¹' S n) :=
          hc _ (hS_compact n).isClosed.measurableSet hsat
      _ ≤ c * μQ ((fun q => q * (gQ n)⁻¹) ⁻¹' W) := by gcongr; exact hpiece n
      _ = _ := by rw [measure_preimage_mul_right_inv hQ μQ W (gQ n), hmod n]
  calc μ (ΩU * ΩM * C * K) ≤ μ (⋃ n, S n) := measure_mono hsub
    _ ≤ ∑' n, μ (S n) := measure_iUnion_le _
    _ ≤ ∑' n, c * (((HaarModulus.closedNormalizerCharacter U hU
          ⟨g n, h.levi_le_normalizer (hgM n)⟩ : ℝ≥0) : ℝ≥0∞)⁻¹ * μQ W) :=
        ENNReal.tsum_le_tsum hbound
    _ = c * ((∑' n, ((HaarModulus.closedNormalizerCharacter U hU
          ⟨g n, h.levi_le_normalizer (hgM n)⟩ : ℝ≥0) : ℝ≥0∞)⁻¹) * μQ W) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top
        (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hsum) hW)

/-- **Chamber Siegel-set bound.** With `a : A →* H` landing in the centre of `M`
and commuting with `K ∩ Q`, finitely many characters `λ_i` whose box
`1/2 ≤ λ_i ≤ 2` is compact, and `∏ λ_i ^ e_i ≤ δ_U ∘ a` with every `e_i ≥ 1`, the
set `ΩU ΩM a(t ≤ λ) K` has finite Haar measure. -/
theorem measure_mul_chamber_mul_lt_top (μ : Measure H) {Q M U K : Subgroup H}
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
    (e : ι → ℕ) (he : ∀ i, e i ≠ 0)
    (hδ : ∀ x, ∏ i, (lam i x : ℝ≥0) ^ e i ≤
      (HaarModulus.closedNormalizerCharacter U hU ⟨a x, h.levi_le_normalizer (haM x)⟩ : ℝ≥0))
    {t : ℝ≥0} (ht : t ≠ 0) :
    μ (ΩU * ΩM * (a '' chamber lam t) * K) < ∞ := by
  classical
  -- index the cover by the dyadic multi-indices that occur
  let J : Set (ι → ℕ) := chamberIndex lam t '' chamber lam t
  have hJ : ∀ κ : J, ∃ y ∈ chamber lam t, chamberIndex lam t y = κ := fun κ => κ.2
  choose y hy hyκ using hJ
  refine measure_mul_mul_mul_lt_top μ hQ hM hU hK h hp μQ c hc hΩU hΩUU hΩM hΩMM
    (hbox.image ha) (by rintro _ ⟨x, -, rfl⟩; exact haM x) (J := J) (fun κ => a (y κ))
    (fun κ => haM _) (fun κ => hacent _) (fun κ k hk hkQ => haK k hk hkQ _) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    let κ : J := ⟨chamberIndex lam t x, x, hx, rfl⟩
    refine ⟨κ, a ((y κ)⁻¹ * x), ⟨_, inv_mul_mem_dyadicBox lam ht hx (hy κ) (hyκ κ).symm, rfl⟩, ?_⟩
    rw [← map_mul, mul_inv_cancel_left]
  · refine ne_top_of_le_ne_top (tsum_prod_geometric_ne_top (ι := ι) ht e) ?_
    calc ∑' κ : J, ((HaarModulus.closedNormalizerCharacter U hU
            ⟨a (y κ), h.levi_le_normalizer (haM (y κ))⟩ : ℝ≥0) : ℝ≥0∞)⁻¹
        ≤ ∑' κ : J, ∏ i, ((t : ℝ≥0∞) ^ e i)⁻¹ * 2⁻¹ ^ (κ : ι → ℕ) i := by
          refine ENNReal.tsum_le_tsum fun κ => ?_
          calc ((HaarModulus.closedNormalizerCharacter U hU
                ⟨a (y κ), h.levi_le_normalizer (haM (y κ))⟩ : ℝ≥0) : ℝ≥0∞)⁻¹
              ≤ ((∏ i, (lam i (y κ) : ℝ≥0) ^ e i : ℝ≥0) : ℝ≥0∞)⁻¹ :=
                ENNReal.inv_le_inv' (ENNReal.coe_le_coe.mpr (hδ (y κ)))
            _ ≤ ∏ i, ((t : ℝ≥0∞) ^ e i)⁻¹ * 2⁻¹ ^ chamberIndex lam t (y κ) i :=
                inv_prod_pow_le lam ht e he (hy κ)
            _ = ∏ i, ((t : ℝ≥0∞) ^ e i)⁻¹ * 2⁻¹ ^ (κ : ι → ℕ) i := by rw [hyκ κ]
      _ ≤ ∑' m : ι → ℕ, ∏ i, ((t : ℝ≥0∞) ^ e i)⁻¹ * 2⁻¹ ^ m i :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun m : ι → ℕ => ∏ i, ((t : ℝ≥0∞) ^ e i)⁻¹ * 2⁻¹ ^ m i)

end Group

end Langlands.SiegelSetMeasure
