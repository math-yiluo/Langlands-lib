import Langlands.Representation.Exponents.Jacquet
import Langlands.LocalField.Uniformizer

/-!
# H-maps and positive root cones for block Levis of `GL_n`

For a block shape `(n_1, …, n_r)` the Levi `M = GL_(n_1) × ⋯ × GL_(n_r)` has the
H-map `H_M(m)_j = log_q |det m_j|`, and its split centre `(F^×)^r` has the H-map
`H(a)_j = log_q |a_j|` (Silberger 1979, 0.4). Both are integer valued.

Real parts of characters of the split centre are vectors `x` with
`|χ(a)| = ∏ |a_j|^(x_j) = q^⟨x, H(a)⟩` (`IsRealPartOf`). In these coordinates the
open positive root cone has total `0` and positive partial sums
`x_1 + ⋯ + x_k > 0` for `0 < k < r`. This is the shape of Casselman's
square-integrability inequality `|χ(a)| < 1` on the negative chamber of the split
centre modulo its compact part and the centre of `GL_n`. The closed cone has
nonnegative partial sums. Both are characterized by the pairing with monotone
integer vectors and by the corresponding inequality for characters.

The determinant-twist coordinates `t`, in which `m ↦ ∏ |det m_j|^(t_j)`, are
related to the split-centre coordinates by `x_j = n_j t_j`
(`isRealPartOf_blockSize_mul_iff`).
-/

noncomputable section

namespace Langlands

universe uF

open Finset

namespace Exponents

variable {r : ℕ}

/-- `x_1 + ⋯ + x_k`: the sum of the coordinates of index below `k`. -/
def partialSum (x : Fin r → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin r => (i : ℕ) < k), x i

/-- The open positive root cone in split-centre coordinates: the coordinates add up
to `0` and every proper initial partial sum is positive. -/
def IsPositiveRootCone (x : Fin r → ℝ) : Prop :=
  ∑ i, x i = 0 ∧ ∀ k : ℕ, 0 < k → k < r → 0 < partialSum x k

/-- The closed positive root cone: total `0` and nonnegative proper partial sums. -/
def IsClosedPositiveRootCone (x : Fin r → ℝ) : Prop :=
  ∑ i, x i = 0 ∧ ∀ k : ℕ, 0 < k → k < r → 0 ≤ partialSum x k

theorem IsPositiveRootCone.isClosedPositiveRootCone {x : Fin r → ℝ}
    (hx : IsPositiveRootCone x) : IsClosedPositiveRootCone x :=
  ⟨hx.1, fun k hk hkr => (hx.2 k hk hkr).le⟩

/-- Extension by zero to all natural indices. -/
private def extend (x : Fin r → ℝ) (i : ℕ) : ℝ :=
  if hi : i < r then x ⟨i, hi⟩ else 0

private theorem extend_lt (x : Fin r → ℝ) {i : ℕ} (hi : i < r) : extend x i = x ⟨i, hi⟩ := by
  simp [extend, hi]

private theorem extend_fin (x : Fin r → ℝ) (i : Fin r) : extend x i = x i :=
  extend_lt x i.isLt

private theorem partialSum_eq_sum_range (x : Fin r → ℝ) {k : ℕ} (hk : k ≤ r) :
    partialSum x k = ∑ i ∈ range k, extend x i := by
  rw [partialSum, Finset.sum_filter]
  have h1 : ∑ i : Fin r, (if (i : ℕ) < k then x i else 0) =
      ∑ i : Fin r, (fun j : ℕ => if j < k then extend x j else 0) (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [extend_fin]
  rw [h1, Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k then extend x j else 0) r,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

private theorem sum_eq_partialSum (x : Fin r → ℝ) : ∑ i, x i = partialSum x r := by
  rw [partialSum]
  congr 1
  ext i
  simp

/-- Summation by parts for a total-zero vector: `⟨x, h⟩` is minus the sum over
`k = 1, …, r - 1` of `(h_k - h_(k-1))` times the `k`-th partial sum. -/
private theorem sum_mul_eq (x h : Fin r → ℝ) (hx : ∑ i, x i = 0) :
    ∑ i, x i * h i =
      -∑ i ∈ range (r - 1), (extend h (i + 1) - extend h i) * partialSum x (i + 1) := by
  have hby := Finset.sum_range_by_parts (extend h) (extend x) r
  simp only [smul_eq_mul] at hby
  have hl : ∑ i, x i * h i = ∑ i ∈ range r, extend h i * extend x i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => extend h i * extend x i) r]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [extend_fin, extend_fin, mul_comm]
  have hr : ∑ i ∈ range r, extend x i = 0 := by
    rw [← partialSum_eq_sum_range x le_rfl, ← sum_eq_partialSum, hx]
  rw [hl, hby, hr, mul_zero, zero_sub, neg_inj]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [partialSum_eq_sum_range x (by rw [mem_range] at hi; omega)]

/-- The vector `(0, …, 0, 1, …, 1)` with `k` leading zeros. -/
private def step (r k : ℕ) : Fin r → ℤ := fun i => if k ≤ (i : ℕ) then 1 else 0

private theorem step_monotone (r k : ℕ) : Monotone (step r k) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  simp only [step]
  split_ifs <;> omega

private theorem sum_mul_step (x : Fin r → ℝ) (k : ℕ) :
    ∑ i, x i * (step r k i : ℝ) = ∑ i, x i - partialSum x k := by
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun i : Fin r => (i : ℕ) < k) x
  have hstep : ∑ i, x i * (step r k i : ℝ) =
      ∑ i ∈ univ.filter (fun i : Fin r => ¬ (i : ℕ) < k), x i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [step]
    split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp
  rw [hstep, partialSum, ← hsplit]
  ring

/-- If the step from `h_k` to `h_(k+1)` is never positive below `r - 1`, a monotone
`h` is constant. -/
private theorem exists_step_pos {h : Fin r → ℤ} (hmono : Monotone h)
    (hne : ∃ i j, h i ≠ h j) :
    ∃ k, ∃ hk : k + 1 < r, h ⟨k, by omega⟩ < h ⟨k + 1, hk⟩ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, j, hij⟩ := hne
  have hr : 0 < r := by have := i.isLt; omega
  have hconst : ∀ m (hm : m < r), h ⟨m, hm⟩ = h ⟨0, hr⟩ := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hle : h ⟨m, by omega⟩ ≤ h ⟨m + 1, hm⟩ :=
        hmono (show (⟨m, by omega⟩ : Fin r) ≤ ⟨m + 1, hm⟩ from Fin.mk_le_mk.mpr (by omega))
      have hge := hcon m hm
      rw [← ih (by omega)]
      omega
  exact hij ((hconst i i.isLt).trans (hconst j j.isLt).symm)

/-- The open cone is the set of total-zero vectors with negative pairing against
every nonconstant monotone integer vector. -/
theorem isPositiveRootCone_iff_pairing (x : Fin r → ℝ) :
    IsPositiveRootCone x ↔
      ∑ i, x i = 0 ∧
        ∀ h : Fin r → ℤ, Monotone h → (∃ i j, h i ≠ h j) → ∑ i, x i * (h i : ℝ) < 0 := by
  constructor
  · rintro ⟨hx, hpos⟩
    refine ⟨hx, fun h hmono hne => ?_⟩
    rw [sum_mul_eq x (fun i => (h i : ℝ)) hx, neg_lt_zero]
    obtain ⟨k, hk, hlt⟩ := exists_step_pos hmono hne
    refine Finset.sum_pos' (fun i hi => ?_) ⟨k, mem_range.mpr (by omega), ?_⟩
    · rw [mem_range] at hi
      rw [extend_lt _ (show i + 1 < r by omega), extend_lt _ (show i < r by omega)]
      have hmi : h ⟨i, by omega⟩ ≤ h ⟨i + 1, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hd : (0 : ℝ) ≤ (h ⟨i + 1, by omega⟩ : ℝ) - (h ⟨i, by omega⟩ : ℝ) := by
        rw [sub_nonneg]; exact_mod_cast hmi
      exact mul_nonneg hd (hpos (i + 1) (by omega) (by omega)).le
    · rw [extend_lt _ hk, extend_lt _ (show k < r by omega)]
      have hd : (0 : ℝ) < (h ⟨k + 1, hk⟩ : ℝ) - (h ⟨k, by omega⟩ : ℝ) := by
        rw [sub_pos]; exact_mod_cast hlt
      exact mul_pos hd (hpos (k + 1) (by omega) hk)
  · rintro ⟨hx, hneg⟩
    refine ⟨hx, fun k hk hkr => ?_⟩
    have hne : ∃ i j, step r k i ≠ step r k j :=
      ⟨⟨0, by omega⟩, ⟨k, hkr⟩, by simp only [step]; split_ifs <;> omega⟩
    have h := hneg (step r k) (step_monotone r k) hne
    rw [sum_mul_step, hx] at h
    linarith

/-- The closed cone is the set of total-zero vectors with nonpositive pairing
against every monotone integer vector. -/
theorem isClosedPositiveRootCone_iff_pairing (x : Fin r → ℝ) :
    IsClosedPositiveRootCone x ↔
      ∑ i, x i = 0 ∧ ∀ h : Fin r → ℤ, Monotone h → ∑ i, x i * (h i : ℝ) ≤ 0 := by
  constructor
  · rintro ⟨hx, hnn⟩
    refine ⟨hx, fun h hmono => ?_⟩
    rw [sum_mul_eq x (fun i => (h i : ℝ)) hx, neg_nonpos]
    refine Finset.sum_nonneg fun i hi => ?_
    rw [mem_range] at hi
    rw [extend_lt _ (show i + 1 < r by omega), extend_lt _ (show i < r by omega)]
    have hmi : h ⟨i, by omega⟩ ≤ h ⟨i + 1, by omega⟩ := hmono (Fin.mk_le_mk.mpr (by omega))
    have hd : (0 : ℝ) ≤ (h ⟨i + 1, by omega⟩ : ℝ) - (h ⟨i, by omega⟩ : ℝ) := by
      rw [sub_nonneg]; exact_mod_cast hmi
    exact mul_nonneg hd (hnn (i + 1) (by omega) (by omega))
  · rintro ⟨hx, hnp⟩
    refine ⟨hx, fun k hk hkr => ?_⟩
    have h := hnp (step r k) (step_monotone r k)
    rw [sum_mul_step, hx] at h
    linarith

/-- The simple root `e_(k-1) - e_k`, with coordinates indexed from `0`; it is a root
of the block Levi split centre for `0 < k < r`. -/
def simpleRoot (r k : ℕ) : Fin r → ℝ := fun i =>
  if (i : ℕ) + 1 = k then 1 else if (i : ℕ) = k then -1 else 0

private theorem partialSum_zero (x : Fin r → ℝ) : partialSum x 0 = 0 := by
  simp [partialSum]

private theorem partialSum_succ (x : Fin r → ℝ) {i : ℕ} (hi : i < r) :
    partialSum x (i + 1) = partialSum x i + x ⟨i, hi⟩ := by
  rw [partialSum_eq_sum_range x (by omega), partialSum_eq_sum_range x hi.le, sum_range_succ,
    extend_lt x hi]

/-- Telescoping partial sums. -/
private theorem partialSum_of_eq_sub {y : Fin r → ℝ} {d : ℕ → ℝ}
    (hy : ∀ i : Fin r, y i = d (i + 1) - d i) : ∀ m, m ≤ r → partialSum y m = d m - d 0 := by
  intro m
  induction m with
  | zero => intro _; rw [partialSum_zero, sub_self]
  | succ m ih =>
    intro hm
    rw [partialSum_succ y (by omega), ih (by omega), hy]
    ring

/-- The coordinates of a combination of simple roots. -/
theorem sum_smul_simpleRoot_apply (c : ℕ → ℝ) (i : Fin r) :
    (∑ k ∈ Ioo 0 r, c k • simpleRoot r k) i =
      (if (i : ℕ) + 1 < r then c (i + 1) else 0) - (if 0 < (i : ℕ) then c i else 0) := by
  rw [Finset.sum_apply]
  have h : ∀ k ∈ Ioo 0 r, (c k • simpleRoot r k) i =
      (if k = (i : ℕ) + 1 then c k else 0) - (if k = (i : ℕ) then c k else 0) := by
    intro k _
    simp only [Pi.smul_apply, smul_eq_mul, simpleRoot]
    split_ifs <;> first | (exfalso; omega) | ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [mem_Ioo]
  have hi := i.isLt
  congr 1
  · split_ifs <;> first | rfl | (exfalso; omega)
  · split_ifs <;> first | rfl | (exfalso; omega)

/-- The open cone consists of the strictly positive combinations of the simple roots
`e_(k-1) - e_k`, `0 < k < r`. The coefficients are the partial sums. -/
theorem isPositiveRootCone_iff_exists_simpleRoot (x : Fin r → ℝ) :
    IsPositiveRootCone x ↔
      ∃ c : ℕ → ℝ, (∀ k, 0 < k → k < r → 0 < c k) ∧ x = ∑ k ∈ Ioo 0 r, c k • simpleRoot r k := by
  constructor
  · rintro ⟨hx, hpos⟩
    refine ⟨partialSum x, hpos, funext fun i => ?_⟩
    obtain ⟨i, hi⟩ := i
    rw [sum_smul_simpleRoot_apply]
    simp only
    have hs := partialSum_succ x hi
    have hr : partialSum x r = 0 := by rw [← sum_eq_partialSum, hx]
    have h0 := partialSum_zero x
    split_ifs with h1 h2 h2
    · rw [hs]; ring
    · obtain rfl : i = 0 := by omega
      linarith
    · obtain rfl : r = i + 1 := by omega
      linarith
    · obtain rfl : i = 0 := by omega
      obtain rfl : r = 1 := by omega
      have hr' : partialSum x (0 + 1) = 0 := hr
      linarith
  · rintro ⟨c, hc, rfl⟩
    let d : ℕ → ℝ := fun m => if 0 < m ∧ m < r then c m else 0
    have hy : ∀ i : Fin r, (∑ k ∈ Ioo 0 r, c k • simpleRoot r k) i = d (i + 1) - d i := by
      intro i
      rw [sum_smul_simpleRoot_apply]
      simp only [d]
      have hi := i.isLt
      congr 1
      · split_ifs <;> first | rfl | (exfalso; omega)
      · split_ifs <;> first | rfl | (exfalso; omega)
    have hp := partialSum_of_eq_sub hy
    have hd0 : d 0 = 0 := by simp [d]
    refine ⟨?_, fun k hk hkr => ?_⟩
    · rw [sum_eq_partialSum, hp r le_rfl, hd0]
      simp [d]
    · rw [hp k hkr.le, hd0, sub_zero]
      simpa [d, hk, hkr] using hc k hk hkr

end Exponents

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- `log_q |a|` for a unit `a`, that is `-ord a`. -/
def logAbs (a : F.Carrierˣ) : ℤ := -T.ord (a : F.Carrier)

theorem normalizedAbs_eq_zpow_logAbs (a : F.Carrierˣ) :
    T.normalizedAbs (a : F.Carrier) = (T.residueCardinality : ℝ) ^ T.logAbs a :=
  T.normalizedAbs_of_ne_zero a.ne_zero

@[simp]
theorem logAbs_mul (a b : F.Carrierˣ) : T.logAbs (a * b) = T.logAbs a + T.logAbs b := by
  simp only [logAbs, Units.val_mul, T.ord_mul a.ne_zero b.ne_zero]
  ring

@[simp]
theorem logAbs_one : T.logAbs 1 = 0 := by
  simp [logAbs, T.ord_one]

theorem logAbs_pow (a : F.Carrierˣ) (k : ℕ) : T.logAbs (a ^ k) = k * T.logAbs a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, logAbs_mul, ih]; push_cast; ring

theorem logAbs_le_logAbs_iff (a b : F.Carrierˣ) :
    T.logAbs a ≤ T.logAbs b ↔ T.normalizedAbs (a : F.Carrier) ≤ T.normalizedAbs (b : F.Carrier) := by
  rw [T.normalizedAbs_eq_zpow_logAbs, T.normalizedAbs_eq_zpow_logAbs,
    zpow_le_zpow_iff_right₀ (by exact_mod_cast T.residueCardinality_gt_one)]

theorem logAbs_eq_logAbs_iff (a b : F.Carrierˣ) :
    T.logAbs a = T.logAbs b ↔ T.normalizedAbs (a : F.Carrier) = T.normalizedAbs (b : F.Carrier) := by
  rw [le_antisymm_iff, le_antisymm_iff, T.logAbs_le_logAbs_iff, T.logAbs_le_logAbs_iff]

private theorem logAbs_uniformizerUnit_zpow (m : ℤ) : T.logAbs ((LocalFactor.PadicAbelian.uniformizerUnit T) ^ m) = -m := by
  simp only [logAbs, Units.val_zpow_eq_zpow_val, LocalFactor.PadicAbelian.uniformizerUnit_coe, T.ord_zpow,
    T.ord_uniformizer, mul_one]

/-- The H-map of the split centre `(F^×)^r`: `H(a)_j = log_q |a_j|`. -/
def centreHMap {r : ℕ} (a : Fin r → F.Carrierˣ) : Fin r → ℤ := fun j => T.logAbs (a j)

@[simp]
theorem centreHMap_apply {r : ℕ} (a : Fin r → F.Carrierˣ) (j : Fin r) :
    T.centreHMap a j = T.logAbs (a j) := rfl

theorem centreHMap_mul {r : ℕ} (a b : Fin r → F.Carrierˣ) :
    T.centreHMap (a * b) = T.centreHMap a + T.centreHMap b :=
  funext fun j => T.logAbs_mul (a j) (b j)

theorem centreHMap_one {r : ℕ} : T.centreHMap (1 : Fin r → F.Carrierˣ) = 0 :=
  funext fun _ => T.logAbs_one

private theorem centreHMap_uniformizer_zpow {r : ℕ} (h : Fin r → ℤ) :
    T.centreHMap (fun j => (LocalFactor.PadicAbelian.uniformizerUnit T) ^ (-h j)) = h :=
  funext fun j => by rw [centreHMap_apply, T.logAbs_uniformizerUnit_zpow, neg_neg]

/-- Every integer vector is the H-map of a vector of powers of a uniformizer. -/
theorem centreHMap_surjective {r : ℕ} : Function.Surjective (T.centreHMap (r := r)) :=
  fun h => ⟨_, T.centreHMap_uniformizer_zpow h⟩

/-- The H-map of the block Levi: `H_M(m)_j = log_q |det m_j|`. -/
def leviHMap {n : ℕ} (B : GeneralLinear.BlockShape n) (m : B.Levi F.Carrier) :
    Fin B.length → ℤ :=
  fun j => T.logAbs (GeneralLinear.determinant (m j))

variable {n : ℕ} (B : GeneralLinear.BlockShape n)

@[simp]
theorem leviHMap_apply (m : B.Levi F.Carrier) (j : Fin B.length) :
    T.leviHMap B m j = T.logAbs (GeneralLinear.determinant (m j)) := rfl

theorem leviHMap_mul (m m' : B.Levi F.Carrier) :
    T.leviHMap B (m * m') = T.leviHMap B m + T.leviHMap B m' :=
  funext fun j => by
    simp only [leviHMap_apply, Pi.add_apply, Pi.mul_apply, map_mul, logAbs_mul]

theorem leviHMap_one : T.leviHMap B 1 = 0 :=
  funext fun j => by simp

/-- `|det m_j| = q^(H_M(m)_j)`. -/
theorem determinantNorm_eq_zpow_leviHMap (m : B.Levi F.Carrier) (j : Fin B.length) :
    ((T.determinantNorm (B.size j) (m j) : NNReal) : ℝ) =
      (T.residueCardinality : ℝ) ^ T.leviHMap B m j :=
  T.normalizedAbs_eq_zpow_logAbs _

/-- On block scalars the Levi H-map is the split-centre H-map weighted by the block
sizes. -/
theorem leviHMap_blockScalarLevi (a : Fin B.length → F.Carrierˣ) (j : Fin B.length) :
    T.leviHMap B (B.blockScalarLevi F.Carrier a) j = B.size j * T.centreHMap a j := by
  change T.logAbs (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin (B.size j)) (a j))) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, logAbs_pow, centreHMap_apply]

/-- `∏ |a_j|^(x_j) = q^⟨x, H(a)⟩`. -/
theorem prod_normalizedAbs_rpow {r : ℕ} (a : Fin r → F.Carrierˣ) (x : Fin r → ℝ) :
    ∏ j, T.normalizedAbs (a j : F.Carrier) ^ x j =
      (T.residueCardinality : ℝ) ^ ∑ j, x j * (T.centreHMap a j : ℝ) := by
  have hq : (0 : ℝ) < T.residueCardinality := by
    exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)
  rw [Real.rpow_sum_of_pos hq]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [T.normalizedAbs_eq_zpow_logAbs, ← Real.rpow_intCast, ← Real.rpow_mul hq.le,
    centreHMap_apply, mul_comm]

/-- The real part in H-map form: `|χ(a)| = q^⟨x, H(a)⟩`. -/
theorem isRealPartOf_iff_pairing {r : ℕ} (χ : (Fin r → F.Carrierˣ) →* ℂˣ) (x : Fin r → ℝ) :
    T.IsRealPartOf χ x ↔
      ∀ a, ‖(χ a : ℂ)‖ = (T.residueCardinality : ℝ) ^ ∑ j, x j * (T.centreHMap a j : ℝ) := by
  simp only [IsRealPartOf, prod_normalizedAbs_rpow]

/-- Determinant-twist coordinates: `x` with `x_j = n_j t_j` is the real part of `χ`
exactly when `|χ(a)| = ∏ |det(a_j 1_(n_j))|^(t_j)`. -/
theorem isRealPartOf_blockSize_mul_iff (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (t : Fin B.length → ℝ) :
    T.IsRealPartOf χ (fun j => (B.size j : ℝ) * t j) ↔
      ∀ a, ‖(χ a : ℂ)‖ =
        ∏ j, ((T.determinantNorm (B.size j) (B.blockScalarLevi F.Carrier a j) : NNReal) : ℝ) ^
          t j := by
  have h : ∀ (a : Fin B.length → F.Carrierˣ) (j : Fin B.length),
      ((T.determinantNorm (B.size j) (B.blockScalarLevi F.Carrier a j) : NNReal) : ℝ) ^ t j =
        T.normalizedAbs (a j : F.Carrier) ^ ((B.size j : ℝ) * t j) := by
    intro a j
    change ((T.determinantNorm (B.size j) (GeneralLinear.scalar (a j)) : NNReal) : ℝ) ^ t j = _
    rw [T.determinantNorm_scalar, Real.rpow_natCast_mul (T.normalizedAbs_nonneg _)]
    simp
  simp only [IsRealPartOf, h]

theorem one_lt_residueCardinality_real : (1 : ℝ) < T.residueCardinality := by
  exact_mod_cast T.residueCardinality_gt_one

private theorem rpow_lt_one_iff' (y : ℝ) : (T.residueCardinality : ℝ) ^ y < 1 ↔ y < 0 := by
  conv_lhs => rw [← Real.rpow_zero (T.residueCardinality : ℝ)]
  exact Real.rpow_lt_rpow_left_iff T.one_lt_residueCardinality_real

private theorem rpow_le_one_iff' (y : ℝ) : (T.residueCardinality : ℝ) ^ y ≤ 1 ↔ y ≤ 0 := by
  conv_lhs => rw [← Real.rpow_zero (T.residueCardinality : ℝ)]
  exact Real.rpow_le_rpow_left_iff T.one_lt_residueCardinality_real

private theorem rpow_eq_one_iff' (y : ℝ) : (T.residueCardinality : ℝ) ^ y = 1 ↔ y = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy y 0 with hlt | heq | hgt
    · exact absurd h ((T.rpow_lt_one_iff' y).mpr hlt).ne
    · exact heq
    · have hn : ¬ (T.residueCardinality : ℝ) ^ y ≤ 1 := by
        rw [T.rpow_le_one_iff']
        linarith
      exact absurd h.le hn
  · rintro rfl
    exact Real.rpow_zero _

variable {T}

/-- The real part has total `0` exactly when `χ` is unitary on the diagonal scalars
`(c, …, c)`. -/
theorem IsRealPartOf.sum_eq_zero_iff {r : ℕ} {χ : (Fin r → F.Carrierˣ) →* ℂˣ} {x : Fin r → ℝ}
    (hx : T.IsRealPartOf χ x) :
    ∑ j, x j = 0 ↔ ∀ c : F.Carrierˣ, ‖(χ (fun _ => c) : ℂ)‖ = 1 := by
  rw [isRealPartOf_iff_pairing] at hx
  have hc : ∀ c : F.Carrierˣ, ‖(χ (fun _ => c) : ℂ)‖ =
      (T.residueCardinality : ℝ) ^ ((∑ j, x j) * (T.logAbs c : ℝ)) := by
    intro c
    rw [hx, Finset.sum_mul]
    rfl
  constructor
  · intro h0 c
    rw [hc, h0, zero_mul, Real.rpow_zero]
  · intro h1
    have h := h1 (LocalFactor.PadicAbelian.uniformizerUnit T)
    rw [hc, T.rpow_eq_one_iff'] at h
    have hu : T.logAbs (LocalFactor.PadicAbelian.uniformizerUnit T) = -1 := by
      simpa using T.logAbs_uniformizerUnit_zpow 1
    rw [hu] at h
    push_cast at h
    linarith

private theorem monotone_centreHMap_iff {r : ℕ} (a : Fin r → F.Carrierˣ) :
    Monotone (T.centreHMap a) ↔ Monotone fun j => T.normalizedAbs (a j : F.Carrier) := by
  simp only [Monotone, centreHMap_apply, T.logAbs_le_logAbs_iff]

private theorem exists_ne_centreHMap_iff {r : ℕ} (a : Fin r → F.Carrierˣ) :
    (∃ i j, T.centreHMap a i ≠ T.centreHMap a j) ↔
      ∃ i j, T.normalizedAbs (a i : F.Carrier) ≠ T.normalizedAbs (a j : F.Carrier) := by
  simp only [ne_eq, centreHMap_apply, T.logAbs_eq_logAbs_iff]

/-- Casselman's form of the open cone: the real part `x` of `χ` lies in the open
positive root cone exactly when `χ` is unitary on the diagonal scalars and
`|χ(a)| < 1` for every `a` with `|a_1| ≤ ⋯ ≤ |a_r|` whose absolute values are not
all equal. -/
theorem IsRealPartOf.isPositiveRootCone_iff {r : ℕ} {χ : (Fin r → F.Carrierˣ) →* ℂˣ}
    {x : Fin r → ℝ} (hx : T.IsRealPartOf χ x) :
    Exponents.IsPositiveRootCone x ↔
      (∀ c : F.Carrierˣ, ‖(χ (fun _ => c) : ℂ)‖ = 1) ∧
        ∀ a : Fin r → F.Carrierˣ, Monotone (fun j => T.normalizedAbs (a j : F.Carrier)) →
          (∃ i j, T.normalizedAbs (a i : F.Carrier) ≠ T.normalizedAbs (a j : F.Carrier)) →
            ‖(χ a : ℂ)‖ < 1 := by
  rw [Exponents.isPositiveRootCone_iff_pairing, hx.sum_eq_zero_iff]
  rw [isRealPartOf_iff_pairing] at hx
  refine and_congr_right fun _ => ⟨fun h a hmono hne => ?_, fun h hv hmono hne => ?_⟩
  · rw [hx, T.rpow_lt_one_iff']
    exact h _ ((monotone_centreHMap_iff a).mpr hmono) ((exists_ne_centreHMap_iff a).mpr hne)
  · have ha := h (fun j => (LocalFactor.PadicAbelian.uniformizerUnit T) ^ (-hv j))
      ((monotone_centreHMap_iff _).mp (by rw [T.centreHMap_uniformizer_zpow]; exact hmono))
      ((exists_ne_centreHMap_iff _).mp (by rw [T.centreHMap_uniformizer_zpow]; exact hne))
    rwa [hx, T.rpow_lt_one_iff', T.centreHMap_uniformizer_zpow] at ha

/-- Casselman's form of the closed cone: `χ` is unitary on the diagonal scalars and
`|χ(a)| ≤ 1` whenever `|a_1| ≤ ⋯ ≤ |a_r|`. -/
theorem IsRealPartOf.isClosedPositiveRootCone_iff {r : ℕ} {χ : (Fin r → F.Carrierˣ) →* ℂˣ}
    {x : Fin r → ℝ} (hx : T.IsRealPartOf χ x) :
    Exponents.IsClosedPositiveRootCone x ↔
      (∀ c : F.Carrierˣ, ‖(χ (fun _ => c) : ℂ)‖ = 1) ∧
        ∀ a : Fin r → F.Carrierˣ, Monotone (fun j => T.normalizedAbs (a j : F.Carrier)) →
          ‖(χ a : ℂ)‖ ≤ 1 := by
  rw [Exponents.isClosedPositiveRootCone_iff_pairing, hx.sum_eq_zero_iff]
  rw [isRealPartOf_iff_pairing] at hx
  refine and_congr_right fun _ => ⟨fun h a hmono => ?_, fun h hv hmono => ?_⟩
  · rw [hx, T.rpow_le_one_iff']
    exact h _ ((monotone_centreHMap_iff a).mpr hmono)
  · have ha := h (fun j => (LocalFactor.PadicAbelian.uniformizerUnit T) ^ (-hv j))
      ((monotone_centreHMap_iff _).mp (by rw [T.centreHMap_uniformizer_zpow]; exact hmono))
    rwa [hx, T.rpow_le_one_iff', T.centreHMap_uniformizer_zpow] at ha

end PadicField.TopologicalData

end Langlands
