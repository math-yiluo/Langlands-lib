import Langlands.Group.GL.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Entrywise congruence neighbourhoods in `GL_n` of an ultrametric normed field

For a normed field `𝕂` with an ultrametric norm, `normCongruence 𝕂 n r` is the set of
`g ∈ GL_n(𝕂)` with `‖g i j - δ i j‖ ≤ r` for all `i, j`; for `0 ≤ r < 1` it is a subgroup
(`normCongruenceSubgroup`), open for `r > 0`, compact when `𝕂` is proper, and preserved by
isometric ring homomorphisms. For `0 ≤ r < ‖q‖`: the intertwining lemma (`A^q g = g B^q` implies
`A g = g B` for `A`, `B` entrywise `r`-close to `1`), the power map sends `normCongruence 𝕂 n r`
into `normCongruence 𝕂 n (r * ‖q‖)`, onto it when `𝕂` is proper, with unique roots; and the
twisted descent: for an isometric ring endomorphism `τ` of order dividing `q`, every element of
`u₀ · normCongruence 𝕂 n (ρ * ‖q‖)` is `τ`-conjugate by an element of `normCongruence 𝕂 n ρ` to
`u₀ u` with `u` a `τ`-fixed element of `normCongruence 𝕂 n ρ`. See the paired Markdown.
-/

noncomputable section

open Matrix Set Filter Topology

namespace Langlands.GeneralLinear

universe u

variable {𝕂 : Type u} [NormedField 𝕂] [IsUltrametricDist 𝕂] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) 𝕂

/-- Entrywise bound `‖M i j‖ ≤ c`. -/
private def Bd (c : ℝ) (M : Mat) : Prop := ∀ i j, ‖M i j‖ ≤ c

omit [IsUltrametricDist 𝕂] in
private theorem Bd.mono {a b : ℝ} {M : Mat} (h : Bd a M) (hab : a ≤ b) : Bd b M :=
  fun i j => (h i j).trans hab

omit [IsUltrametricDist 𝕂] in
private theorem Bd.zero {a : ℝ} (ha : 0 ≤ a) : Bd a (0 : Mat) := fun i j => by simpa using ha

private theorem Bd.add {a : ℝ} {M N : Mat} (h : Bd a M) (h' : Bd a N) : Bd a (M + N) :=
  fun i j => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i j) (h' i j))

omit [IsUltrametricDist 𝕂] in
private theorem Bd.neg {a : ℝ} {M : Mat} (h : Bd a M) : Bd a (-M) := fun i j => by
  simpa using h i j

private theorem Bd.sub {a : ℝ} {M N : Mat} (h : Bd a M) (h' : Bd a N) : Bd a (M - N) := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

private theorem Bd.mul {a b : ℝ} {M N : Mat} (h : Bd a M) (h' : Bd b N) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : Bd (a * b) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (h i k) (h' k j) (norm_nonneg _) ha

omit [IsUltrametricDist 𝕂] in
private theorem Bd.smul {a : ℝ} {M : Mat} (h : Bd a M) (x : 𝕂) : Bd (‖x‖ * a) (x • M) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (h i j) (norm_nonneg x)

private theorem Bd.nsmul {a : ℝ} {M : Mat} (h : Bd a M) (ha : 0 ≤ a) (m : ℕ) : Bd a (m • M) := by
  induction m with
  | zero => simpa using Bd.zero ha
  | succ m ih => rw [succ_nsmul]; exact ih.add h

omit [IsUltrametricDist 𝕂] in
private theorem Bd.one : Bd 1 (1 : Mat) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem Bd.of_sub_one {a : ℝ} {M : Mat} (h : Bd a (M - 1)) (ha : a ≤ 1) : Bd 1 M := by
  simpa using (h.mono ha).add Bd.one

/-- `‖(1 + M)^m - 1 - m M‖ ≤ a²` entrywise when `‖M‖ ≤ a ≤ 1`. -/
private theorem Bd.pow {a : ℝ} {M : Mat} (h : Bd a M) (ha₀ : 0 ≤ a) (ha : a ≤ 1) (m : ℕ) :
    Bd (a * a) ((1 + M) ^ m - 1 - m • M) := by
  induction m with
  | zero => intro i j; simpa using mul_nonneg ha₀ ha₀
  | succ m ih =>
    have e : (1 + M) ^ (m + 1) - 1 - (m + 1) • M =
        ((1 + M) ^ m - 1 - m • M) + ((1 + M) ^ m - 1 - m • M) * M + (m • M) * M := by
      rw [pow_succ, succ_nsmul]
      generalize m • M = D
      noncomm_ring
    rw [e]
    have h1 : Bd (a * a) (((1 + M) ^ m - 1 - m • M) * M) :=
      ((ih.mul h (mul_nonneg ha₀ ha₀) ha₀).mono (by nlinarith [mul_nonneg ha₀ ha₀]))
    exact (ih.add h1).add ((h.nsmul ha₀ m).mul h ha₀ ha₀)

/-- `‖M^m - 1‖ ≤ a` entrywise when `‖M - 1‖ ≤ a ≤ 1`. -/
private theorem Bd.pow_sub_one {a : ℝ} {M : Mat} (h : Bd a (M - 1)) (ha₀ : 0 ≤ a) (ha : a ≤ 1)
    (m : ℕ) : Bd a (M ^ m - 1) := by
  induction m with
  | zero => simpa using Bd.zero ha₀
  | succ m ih =>
    have e : M ^ (m + 1) - 1 = (M ^ m - 1) * M + (M - 1) := by
      rw [pow_succ]; noncomm_ring
    rw [e]
    exact Bd.add (by simpa using ih.mul (h.of_sub_one ha) ha₀ zero_le_one) h

/-- The telescoping estimate behind the intertwining lemma (source `RootConj`). -/
private theorem Bd.tele {r c : ℝ} {A B g : Mat} (hr₀ : 0 ≤ r) (hr : r ≤ 1) (hc : 0 ≤ c)
    (hA : Bd r (A - 1)) (hB : Bd r (B - 1)) (hh : Bd c (A * g - g * B)) (m : ℕ) :
    Bd (r * c) (A ^ m * g - g * B ^ m - (m : 𝕂) • (A * g - g * B)) := by
  induction m with
  | zero => intro i j; simpa using mul_nonneg hr₀ hc
  | succ m ih =>
    have hrc : r * c ≤ c := by nlinarith
    have hm : Bd c ((m : 𝕂) • (A * g - g * B)) := by
      rw [Nat.cast_smul_eq_nsmul]; exact hh.nsmul hc m
    have h1 := hA.mul ((ih.mono hrc).add hm) hr₀ hc
    have h2 := (hh.mul (hB.pow_sub_one hr₀ hr m) hc hr₀).mono (mul_comm c r).le
    have e : A ^ (m + 1) * g - g * B ^ (m + 1) - ((m + 1 : ℕ) : 𝕂) • (A * g - g * B) =
        (A - 1) * (A ^ m * g - g * B ^ m - (m : 𝕂) • (A * g - g * B) +
          (m : 𝕂) • (A * g - g * B)) +
          (A * g - g * B) * (B ^ m - 1) + (A ^ m * g - g * B ^ m - (m : 𝕂) • (A * g - g * B)) := by
      rw [Nat.cast_succ, add_smul, one_smul, pow_succ', pow_succ']
      generalize (m : 𝕂) • (A * g - g * B) = Z
      noncomm_ring
    rw [e]; exact (h1.add h2).add ih

/-- The intertwining lemma: if `A` and `B` are entrywise `r`-close to `1` with `r < ‖q‖`, then
`A^q g = g B^q` implies `A g = g B`. -/
theorem mul_eq_mul_of_pow_mul_eq_mul_pow {r : ℝ} {q : ℕ} (hr₀ : 0 ≤ r) (hq : r < ‖(q : 𝕂)‖)
    {A B g : Mat} (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) (hB : ∀ i j, ‖(B - 1) i j‖ ≤ r)
    (h : A ^ q * g = g * B ^ q) : A * g = g * B := by
  rw [← sub_eq_zero]
  ext i0 j0
  obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => ‖(A * g - g * B) p.1 p.2‖) ⟨(i0, j0), Finset.mem_univ _⟩
  have hh : Bd ‖(A * g - g * B) i j‖ (A * g - g * B) := fun a b => hmax (a, b) (Finset.mem_univ _)
  have hr1 : r ≤ 1 := hq.le.trans (IsUltrametricDist.norm_natCast_le_one 𝕂 q)
  have ht := Bd.tele hr₀ hr1 (norm_nonneg _) hA hB hh q i j
  rw [h, sub_self, zero_sub, Matrix.neg_apply, norm_neg, Matrix.smul_apply, smul_eq_mul,
    norm_mul] at ht
  have h0 : ‖(A * g - g * B) i j‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖(A * g - g * B) i j‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  have := hh i0 j0
  rw [h0] at this
  simpa using norm_le_zero_iff.mp this


private theorem Bd.pow_sub_pow {a b : ℝ} {M N : Mat} (hM : Bd a (M - 1)) (hN : Bd a (N - 1))
    (ha₀ : 0 ≤ a) (ha : a ≤ 1) (hb : 0 ≤ b) (hd : Bd b (M - N)) (m : ℕ) :
    Bd (a * b) (M ^ m - N ^ m - m • (M - N)) := by
  induction m with
  | zero => simpa using Bd.zero (mul_nonneg ha₀ hb)
  | succ m ih =>
    have e : M ^ (m + 1) - N ^ (m + 1) - (m + 1) • (M - N) =
        M * (M ^ m - N ^ m - m • (M - N)) + (M - 1) * (m • (M - N)) + (M - N) * (N ^ m - 1) := by
      rw [pow_succ', pow_succ', succ_nsmul]
      generalize m • (M - N) = D
      noncomm_ring
    rw [e]
    refine Bd.add (Bd.add ?_ (hM.mul (hd.nsmul hb m) ha₀ hb)) ?_
    · simpa using (hM.of_sub_one ha).mul ih zero_le_one (mul_nonneg ha₀ hb)
    · rw [mul_comm a b]
      exact hd.mul (hN.pow_sub_one ha₀ ha m) hb ha₀

omit [IsUltrametricDist 𝕂] in
private theorem isClosed_bd (c : ℝ) : IsClosed {M : Mat | Bd c M} := by
  have : {M : Mat | Bd c M} = ⋂ i, ⋂ j, {M : Mat | ‖M i j‖ ≤ c} := by
    ext M; simp [Bd]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le ((continuous_apply j).comp (continuous_apply i)).norm continuous_const

omit [IsUltrametricDist 𝕂] in
private theorem isCompact_bd [ProperSpace 𝕂] (c : ℝ) : IsCompact {M : Mat | Bd c M} := by
  have : {M : Mat | Bd c M} = Set.pi univ fun _ : Fin n => Set.pi univ fun _ : Fin n =>
      Metric.closedBall (0 : 𝕂) c := by
    ext M
    refine ⟨fun h i _ j _ => ?_, fun h i j => ?_⟩
    · simpa using h i j
    · simpa using h i (Set.mem_univ i) j (Set.mem_univ j)
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

private theorem le_zero_of_le_pow {x c R : ℝ} (hc₀ : 0 ≤ c) (hc : c < 1)
    (h : ∀ m : ℕ, x ≤ c ^ m * R) : x ≤ 0 := by
  have ht : Tendsto (fun m : ℕ => c ^ m * R) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc₀ hc).mul_const R
  exact ge_of_tendsto' ht h

private theorem exists_limit [ProperSpace 𝕂] (a : ℕ → 𝕂) (s : ℕ → ℝ) (hs₀ : ∀ m, 0 ≤ s m)
    (hs : ∀ m, s (m + 1) ≤ s m) (ha : ∀ m, ‖a (m + 1) - a m‖ ≤ s m) :
    ∃ L, ∀ m, ‖L - a m‖ ≤ s m := by
  let S : ℕ → Set 𝕂 := fun m => Metric.closedBall (a m) (s m)
  have hc : ∀ m, IsCompact (S m) := fun m => isCompact_closedBall _ _
  have hn : ∀ m, S (m + 1) ⊆ S m := fun m y hy => by
    simp only [S, Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    have : y - a m = (y - a (m + 1)) + (a (m + 1) - a m) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy.trans (hs m)) (ha m))
  obtain ⟨L, hL⟩ := (hc 0).nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hn
    (fun m => ⟨a m, Metric.mem_closedBall_self (hs₀ m)⟩) (fun m => (hc m).isClosed)
  exact ⟨L, fun m => by simpa [S, dist_eq_norm] using Set.mem_iInter.mp hL m⟩

/-- A contraction of the entrywise `R`-ball of matrices, with constant `c < 1`, has a fixed
point there (source `OpenNear`, `fix_ex`). -/
private theorem exists_fixed [ProperSpace 𝕂] (f : Mat → Mat) {c R : ℝ} (hc₀ : 0 ≤ c)
    (hc : c < 1) (hR : 0 ≤ R) (hm : ∀ x, Bd R x → Bd R (f x))
    (hl : ∀ x y s, 0 ≤ s → Bd R x → Bd R y → Bd s (x - y) → Bd (c * s) (f x - f y)) :
    ∃ x, Bd R x ∧ f x = x := by
  let a : ℕ → Mat := fun m => f^[m] 0
  have hs : ∀ m, a (m + 1) = f (a m) := fun m => Function.iterate_succ_apply' _ _ _
  have hb : ∀ m, Bd R (a m) := by
    intro m
    induction m with
    | zero => exact Bd.zero hR
    | succ m ih => rw [hs]; exact hm _ ih
  have hpos : ∀ m, 0 ≤ c ^ m * R := fun m => mul_nonneg (pow_nonneg hc₀ m) hR
  have hd : ∀ m, Bd (c ^ m * R) (a (m + 1) - a m) := by
    intro m
    induction m with
    | zero => simpa [a] using hb 1
    | succ m ih =>
      have := hl _ _ _ (hpos m) (hb (m + 1)) (hb m) ih
      rw [← hs, ← hs] at this
      rwa [pow_succ', mul_assoc]
  have hdec : ∀ m, c ^ (m + 1) * R ≤ c ^ m * R := fun m =>
    calc c ^ (m + 1) * R = c * (c ^ m * R) := by ring
      _ ≤ 1 * (c ^ m * R) := mul_le_mul_of_nonneg_right hc.le (hpos m)
      _ = c ^ m * R := one_mul _
  choose L hL using fun i j => exists_limit (fun m => a m i j) (fun m => c ^ m * R) hpos hdec
    (fun m => hd m i j)
  have hLR : Bd R (Matrix.of L) := fun i j => by simpa [a] using hL i j 0
  refine ⟨Matrix.of L, hLR, ?_⟩
  ext i j
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_zero_of_le_pow (R := R) hc₀ hc fun m => ?_
  have h1 := hl (Matrix.of L) (a m) _ (hpos m) hLR (hb m) (fun i j => hL i j m) i j
  rw [← hs, ← mul_assoc, ← pow_succ'] at h1
  have h2 := hL i j (m + 1)
  have : f (Matrix.of L) i j - Matrix.of L i j =
      (f (Matrix.of L) - a (m + 1)) i j - (L i j - a (m + 1) i j) := by
    simp
  rw [this]
  rw [sub_eq_add_neg]
  exact ((IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le h1 (by rwa [norm_neg]))).trans (hdec m)

/-- A matrix entrywise `s`-close to `1`, `s < 1`, is invertible. -/
private theorem Bd.isUnit [ProperSpace 𝕂] {s : ℝ} {M : Mat} (h : Bd s M) (hs₀ : 0 ≤ s)
    (hs : s < 1) : IsUnit (1 + M) := by
  obtain ⟨N, -, hN⟩ := exists_fixed (fun N => -M - M * N) hs₀ hs hs₀
    (fun x hx => h.neg.sub ((h.mul hx hs₀ hs₀).mono (by nlinarith)))
    (fun x y t ht _ _ hd => by
      have : (-M - M * x) - (-M - M * y) = -(M * (x - y)) := by noncomm_ring
      rw [this]
      exact (h.mul hd hs₀ ht).neg)
  have : (1 + M) * (1 + N) = 1 := by
    have : (1 + M) * (1 + N) = 1 + (N - (-M - M * N)) := by noncomm_ring
    rw [this, hN, sub_self, add_zero]
  exact IsUnit.of_mul_eq_one _ this

/-- If `M + N + M N = 0` (that is, `(1 + M)(1 + N) = 1`) and `‖M‖ ≤ a < 1` entrywise, then
`‖N‖ ≤ a` entrywise. -/
private theorem Bd.inv {a : ℝ} {M N : Mat} (h : Bd a M) (ha₀ : 0 ≤ a) (ha : a < 1)
    (e : N = -M + -(M * N)) : Bd a N := by
  intro i j
  have : Nonempty (Fin n × Fin n) := ⟨(i, j)⟩
  obtain ⟨p, hp⟩ := Finite.exists_max fun p : Fin n × Fin n => ‖N p.1 p.2‖
  have hN : Bd ‖N p.1 p.2‖ N := fun i j => hp (i, j)
  refine (hp (i, j)).trans ?_
  have h1 : Bd (max a (a * ‖N p.1 p.2‖)) (-M + -(M * N)) :=
    (h.neg.mono (le_max_left _ _)).add ((h.mul hN ha₀ (norm_nonneg _)).neg.mono (le_max_right _ _))
  have h2 := h1 p.1 p.2
  rw [← e] at h2
  rcases le_max_iff.mp h2 with h3 | h3
  · exact h3
  · by_contra h4
    push Not at h4
    have h0 : 0 < ‖N p.1 p.2‖ := lt_of_le_of_lt ha₀ h4
    nlinarith

variable (𝕂 n) in
/-- The entrywise `r`-neighbourhood `{g | ‖g i j - δ i j‖ ≤ r for all i, j}` of `1` in
`GL_n(𝕂)`. -/
def normCongruence (r : ℝ) : Set (GeneralLinear n 𝕂) :=
  {g | ∀ i j, ‖(g : Mat) i j - (1 : Mat) i j‖ ≤ r}

omit [IsUltrametricDist 𝕂] in
theorem mem_normCongruence {r : ℝ} {g : GeneralLinear n 𝕂} :
    g ∈ normCongruence 𝕂 n r ↔ ∀ i j, ‖(g : Mat) i j - (1 : Mat) i j‖ ≤ r :=
  Iff.rfl

omit [IsUltrametricDist 𝕂] in
theorem normCongruence_mono {r s : ℝ} (h : r ≤ s) :
    normCongruence 𝕂 n r ⊆ normCongruence 𝕂 n s :=
  fun _ hg i j => (hg i j).trans h

omit [IsUltrametricDist 𝕂] in
theorem one_mem_normCongruence {r : ℝ} (hr : 0 ≤ r) : (1 : GeneralLinear n 𝕂) ∈ normCongruence 𝕂 n r :=
  fun i j => by simpa using hr

theorem mul_mem_normCongruence {r : ℝ} (hr₀ : 0 ≤ r) (hr : r ≤ 1) {x y : GeneralLinear n 𝕂}
    (hx : x ∈ normCongruence 𝕂 n r) (hy : y ∈ normCongruence 𝕂 n r) :
    x * y ∈ normCongruence 𝕂 n r := by
  have hx' : Bd r ((x : Mat) - 1) := hx
  have hy' : Bd r ((y : Mat) - 1) := hy
  have e : ((x * y : GeneralLinear n 𝕂) : Mat) - 1 =
      ((x : Mat) - 1) + ((y : Mat) - 1) + ((x : Mat) - 1) * ((y : Mat) - 1) := by
    rw [Units.val_mul]; noncomm_ring
  have := (hx'.add hy').add ((hx'.mul hy' hr₀ hr₀).mono (by nlinarith))
  rw [← e] at this
  exact this

theorem inv_mem_normCongruence {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) {x : GeneralLinear n 𝕂}
    (hx : x ∈ normCongruence 𝕂 n r) : x⁻¹ ∈ normCongruence 𝕂 n r := by
  have hx' : Bd r ((x : Mat) - 1) := hx
  refine (hx'.inv hr₀ hr (N := ((x⁻¹ : GeneralLinear n 𝕂) : Mat) - 1) ?_ :)
  rw [mul_sub, sub_mul, Units.mul_inv]
  noncomm_ring

variable (𝕂 n) in
/-- For `0 ≤ r < 1`, `normCongruence 𝕂 n r` is a subgroup of `GL_n(𝕂)`. -/
def normCongruenceSubgroup {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) : Subgroup (GeneralLinear n 𝕂) where
  carrier := normCongruence 𝕂 n r
  one_mem' := one_mem_normCongruence hr₀
  mul_mem' := mul_mem_normCongruence hr₀ hr.le
  inv_mem' := inv_mem_normCongruence hr₀ hr

@[simp]
theorem coe_normCongruenceSubgroup {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) :
    (normCongruenceSubgroup 𝕂 n hr₀ hr : Set (GeneralLinear n 𝕂)) = normCongruence 𝕂 n r :=
  rfl

theorem mem_normCongruenceSubgroup {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) {g : GeneralLinear n 𝕂} :
    g ∈ normCongruenceSubgroup 𝕂 n hr₀ hr ↔ g ∈ normCongruence 𝕂 n r :=
  Iff.rfl

theorem isOpen_normCongruence {r : ℝ} (hr : 0 < r) : IsOpen (normCongruence 𝕂 n r) := by
  have e : normCongruence 𝕂 n r = ⋂ i, ⋂ j, (fun g : GeneralLinear n 𝕂 =>
      (g : Mat) i j - (1 : Mat) i j) ⁻¹' Metric.closedBall 0 r := by
    ext g
    simp [normCongruence]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (IsUltrametricDist.isOpen_closedBall (0 : 𝕂) hr.ne').preimage
      ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem isCompact_normCongruence [ProperSpace 𝕂] {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) :
    IsCompact (normCongruence 𝕂 n r) := by
  let S : Submonoid Mat :=
    { carrier := {M | Bd r (M - 1)}
      one_mem' := by simpa using Bd.zero hr₀
      mul_mem' := by
        intro x y hx hy
        have e : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by noncomm_ring
        change Bd r (x * y - 1)
        rw [e]
        exact ((hx : Bd r (x - 1)).add hy).add (((hx : Bd r (x - 1)).mul hy hr₀ hr₀).mono
          (by nlinarith)) }
  have hS : IsCompact (S : Set Mat) := by
    have : (S : Set Mat) = (fun M : Mat => M - 1) ⁻¹' {M | Bd r M} := rfl
    rw [this]
    exact (Homeomorph.subRight (1 : Mat)).isCompact_preimage.mpr (isCompact_bd r)
  have h := Submonoid.units_isCompact hS
  convert h using 1
  ext g
  change g ∈ normCongruence 𝕂 n r ↔ g ∈ S.units
  rw [Submonoid.mem_units_iff]
  exact ⟨fun hg => ⟨hg, inv_mem_normCongruence hr₀ hr hg⟩, fun hg => hg.1⟩

omit [IsUltrametricDist 𝕂] in
/-- An isometric ring homomorphism preserves and reflects membership. -/
theorem map_mem_normCongruence_iff {𝕃 : Type*} [NormedField 𝕃] (τ : 𝕂 →+* 𝕃)
    (hτ : ∀ x, ‖τ x‖ = ‖x‖) {r : ℝ} (g : GeneralLinear n 𝕂) :
    Matrix.GeneralLinearGroup.map τ g ∈ normCongruence 𝕃 n r ↔ g ∈ normCongruence 𝕂 n r := by
  refine forall₂_congr fun i j => ?_
  have e : ((Matrix.GeneralLinearGroup.map τ g : GeneralLinear n 𝕃) : Matrix (Fin n) (Fin n) 𝕃) i j -
      (1 : Matrix (Fin n) (Fin n) 𝕃) i j = τ ((g : Mat) i j - (1 : Mat) i j) := by
    rw [map_sub]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, hτ]

/-- The `q`-th power of an element of `normCongruence 𝕂 n r`, `r < ‖q‖`, lies in
`normCongruence 𝕂 n (r * ‖q‖)`. -/
theorem pow_mem_normCongruence {r : ℝ} {q : ℕ} (hr₀ : 0 ≤ r) (hq : r < ‖(q : 𝕂)‖)
    {u : GeneralLinear n 𝕂} (hu : u ∈ normCongruence 𝕂 n r) :
    u ^ q ∈ normCongruence 𝕂 n (r * ‖(q : 𝕂)‖) := by
  have hu' : Bd r ((u : Mat) - 1) := hu
  have hr1 : r ≤ 1 := hq.le.trans (IsUltrametricDist.norm_natCast_le_one 𝕂 q)
  have h1 := (hu'.pow hr₀ hr1 q).mono (mul_le_mul_of_nonneg_left hq.le hr₀)
  have h2 : Bd (r * ‖(q : 𝕂)‖) (q • ((u : Mat) - 1)) := by
    rw [← Nat.cast_smul_eq_nsmul 𝕂]
    exact (hu'.smul (q : 𝕂)).mono (le_of_eq (mul_comm _ _))
  have h3 := h1.add h2
  rw [sub_add_cancel, add_sub_cancel, ← Units.val_pow_eq_pow_val] at h3
  exact h3

/-- Two elements `u`, `v` of `normCongruence 𝕂 n r`, `r < ‖q‖`, with `g⁻¹ u^q g = v^q`
satisfy `g⁻¹ u g = v`. -/
theorem conj_eq_of_conj_pow_eq {r : ℝ} {q : ℕ} (hr₀ : 0 ≤ r) (hq : r < ‖(q : 𝕂)‖)
    {u v : GeneralLinear n 𝕂} (hu : u ∈ normCongruence 𝕂 n r) (hv : v ∈ normCongruence 𝕂 n r)
    (g : GeneralLinear n 𝕂) (h : g⁻¹ * u ^ q * g = v ^ q) : g⁻¹ * u * g = v := by
  have h1 : u ^ q * g = g * v ^ q := by rw [← h]; group
  have h2 : (u : Mat) * g = g * v :=
    mul_eq_mul_of_pow_mul_eq_mul_pow hr₀ hq (fun i j => hu i j) (fun i j => hv i j)
      (by simpa using congrArg Units.val h1)
  have h3 : u * g = g * v := Units.ext (by simpa using h2)
  rw [mul_assoc, h3]; group

/-- `q`-th roots in `normCongruence 𝕂 n r`, `r < ‖q‖`, are unique. -/
theorem eq_of_pow_eq {r : ℝ} {q : ℕ} (hr₀ : 0 ≤ r) (hq : r < ‖(q : 𝕂)‖)
    {u v : GeneralLinear n 𝕂} (hu : u ∈ normCongruence 𝕂 n r) (hv : v ∈ normCongruence 𝕂 n r)
    (h : u ^ q = v ^ q) : u = v := by
  simpa using conj_eq_of_conj_pow_eq hr₀ hq hu hv 1 (by simpa using h)

/-- Every element of `normCongruence 𝕂 n (r * ‖q‖)`, `0 ≤ r < ‖q‖`, is the `q`-th power of an
element of `normCongruence 𝕂 n r` (source `RootEx`). -/
theorem exists_pow_eq [ProperSpace 𝕂] {r : ℝ} {q : ℕ} (hr₀ : 0 ≤ r) (hq : r < ‖(q : 𝕂)‖)
    {g : GeneralLinear n 𝕂} (hg : g ∈ normCongruence 𝕂 n (r * ‖(q : 𝕂)‖)) :
    ∃ u ∈ normCongruence 𝕂 n r, u ^ q = g := by
  have hq0 : 0 < ‖(q : 𝕂)‖ := hr₀.trans_lt hq
  have hqne : (q : 𝕂) ≠ 0 := norm_pos_iff.mp hq0
  have hq1 : q ≠ 0 := by rintro rfl; simp at hqne
  have hr1 : r ≤ 1 := hq.le.trans (IsUltrametricDist.norm_natCast_le_one 𝕂 q)
  set w := ‖(q : 𝕂)‖ with hw
  set ρ := r / w with hρ
  have hρ₀ : 0 ≤ ρ := div_nonneg hr₀ hq0.le
  have hρ1 : ρ < 1 := (div_lt_one hq0).mpr hq
  have hρw : ρ * w = r := div_mul_cancel₀ r hq0.ne'
  have hg' : Bd (r * w) ((g : Mat) - 1) := hg
  let S : ℕ → Set Mat := fun k =>
    {X | Bd r X} ∩ {X | Bd (ρ ^ k * (r * w)) ((X + 1) ^ q - (g : Mat))}
  have hcl : ∀ k, IsClosed (S k) := fun k =>
    (isClosed_bd r).inter ((isClosed_bd _).preimage (by fun_prop))
  have hanti : ∀ k, S (k + 1) ⊆ S k := fun k X hX =>
    ⟨hX.1, hX.2.mono (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ₀ hρ1.le k.le_succ)
      (mul_nonneg hr₀ hq0.le))⟩
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, Bd.zero hr₀, ?_⟩
      have := hg'.neg
      simpa using this
    | succ k ih =>
      obtain ⟨X, hX, hX'⟩ := ih
      have hD : Bd (ρ ^ k * r) ((q : 𝕂)⁻¹ • ((X + 1) ^ q - (g : Mat))) := by
        have h := hX'.smul (q : 𝕂)⁻¹
        refine h.mono (le_of_eq ?_)
        rw [norm_inv, ← hw]
        field_simp
      set D := (q : 𝕂)⁻¹ • ((X + 1) ^ q - (g : Mat)) with hDdef
      have hqD : q • D = (X + 1) ^ q - (g : Mat) := by
        rw [hDdef, ← Nat.cast_smul_eq_nsmul 𝕂, smul_inv_smul₀ hqne]
      have hρk : ρ ^ k * r ≤ r := by
        have := pow_le_one₀ hρ₀ hρ1.le (n := k)
        nlinarith
      have hXD : Bd r (X - D) := hX.sub (hD.mono hρk)
      refine ⟨X - D, hXD, ?_⟩
      have h := Bd.pow_sub_pow (M := X + 1) (N := X - D + 1) (a := r) (b := ρ ^ k * r)
        (by simpa using hX) (by simpa using hXD) hr₀ hr1
        (mul_nonneg (pow_nonneg hρ₀ k) hr₀) (by simpa using hD) q
      have e1 : X + 1 - (X - D + 1) = D := by abel
      rw [e1, hqD] at h
      have h' := h.neg
      have e2 : -((X + 1) ^ q - (X - D + 1) ^ q - ((X + 1) ^ q - (g : Mat))) = (X - D + 1) ^ q - (g : Mat) := by
        abel
      rw [e2] at h'
      refine h'.mono (le_of_eq ?_)
      rw [← hρw, pow_succ]
      ring
  obtain ⟨X, hX⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne
    ((isCompact_bd r).of_isClosed_subset (hcl 0) Set.inter_subset_left) hcl
  rw [Set.mem_iInter] at hX
  have hXq : (X + 1) ^ q = (g : Mat) := by
    rw [← sub_eq_zero]
    ext i j
    rw [Matrix.zero_apply, ← norm_le_zero_iff]
    exact le_zero_of_le_pow hρ₀ hρ1 fun k => (hX k).2 i j
  have hunit : IsUnit (X + 1) := (isUnit_pow_iff hq1).mp (hXq ▸ g.isUnit)
  refine ⟨hunit.unit, ?_, Units.ext ?_⟩
  · intro i j
    have := (hX 0).1 i j
    simpa [IsUnit.unit_spec] using this
  · rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hXq]


section Descent

/-- For an isometric ring endomorphism `τ` with `τ^[q] = id` and `q ≠ 0` in `𝕂`, the averages
`t x = q⁻¹ ∑_{j < q} τ^j x` and `p x = q⁻¹ ∑_{j < q} j τ^j x` satisfy `τ (t x) = t x`,
`x = t x + τ (p x) - p x`, and `‖t x‖, ‖p x‖ ≤ ‖x‖ / ‖q‖` (source `OpenNear`, `lin_ex`). -/
private theorem exists_twisted_decomposition (τ : 𝕂 →+* 𝕂) (hτ : ∀ x, ‖τ x‖ = ‖x‖) {q : ℕ}
    (hτq : ∀ x, τ^[q] x = x) (hq : (q : 𝕂) ≠ 0) :
    ∃ t p : 𝕂 →+ 𝕂, (∀ x, τ (t x) = t x) ∧ (∀ x, t x + τ (p x) - p x = x) ∧
      (∀ x, ‖t x‖ ≤ ‖x‖ / ‖(q : 𝕂)‖) ∧ (∀ x, ‖p x‖ ≤ ‖x‖ / ‖(q : 𝕂)‖) := by
  have hiv : ∀ (j : ℕ) x, ‖τ^[j] x‖ = ‖x‖ := fun j x => by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hτ, ih]
  have hadd : ∀ (j : ℕ) x y, τ^[j] (x + y) = τ^[j] x + τ^[j] y := fun j x y =>
    iterate_map_add τ j x y
  have hq0 : 0 < ‖(q : 𝕂)‖ := norm_pos_iff.mpr hq
  refine ⟨AddMonoidHom.mk' (fun x => (∑ j ∈ Finset.range q, τ^[j] x) / q) ?_,
    AddMonoidHom.mk' (fun x => (∑ j ∈ Finset.range q, (j : 𝕂) * τ^[j] x) / q) ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [hadd, Finset.sum_add_distrib, add_div]
  · intro x y
    simp only [hadd, mul_add, Finset.sum_add_distrib, add_div]
  · intro x
    simp only [AddMonoidHom.mk'_apply, map_div₀, map_natCast, map_sum]
    congr 1
    have h1 := Finset.sum_range_succ (fun j => τ^[j] x) q
    have h2 := Finset.sum_range_succ' (fun j => τ^[j] x) q
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id, hτq] at h1 h2
    exact add_right_cancel (h2.symm.trans h1)
  · intro x
    simp only [AddMonoidHom.mk'_apply, map_div₀, map_natCast, map_sum, map_mul]
    have h1 := Finset.sum_range_succ (fun j => (j : 𝕂) * τ^[j] x) q
    have h2 := Finset.sum_range_succ' (fun j => (j : 𝕂) * τ^[j] x) q
    have h3 := Finset.sum_range_succ (fun j => τ^[j] x) q
    have h4 := Finset.sum_range_succ' (fun j => τ^[j] x) q
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id, hτq, Nat.cast_succ,
      add_mul, one_mul, Finset.sum_add_distrib, Nat.cast_zero, zero_mul, add_zero] at h1 h2 h3 h4
    field_simp
    linear_combination h1 - h2 - h3 + h4
  · intro x
    simp only [AddMonoidHom.mk'_apply, norm_div]
    gcongr
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg x)
      fun j _ => (hiv j x).le
  · intro x
    simp only [AddMonoidHom.mk'_apply, norm_div]
    gcongr
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg x) fun j _ => ?_
    rw [norm_mul, hiv]
    exact mul_le_of_le_one_left (norm_nonneg x) (IsUltrametricDist.norm_natCast_le_one 𝕂 j)

/-- Twisted descent near `1` (source `OpenNear`): let `τ` be an isometric ring endomorphism of
`𝕂` with `τ^[q] = id`, and `0 ≤ ρ ≤ r < ‖q‖`. For `u₀` in `normCongruence 𝕂 n r` and `g` in
`normCongruence 𝕂 n (ρ * ‖q‖)` there are `κ` and a `τ`-fixed `u`, both in
`normCongruence 𝕂 n ρ`, with `u₀ g = κ⁻¹ (u₀ u) τ(κ)`. -/
theorem exists_mul_eq_twistedConj [ProperSpace 𝕂] (τ : 𝕂 →+* 𝕂) (hτ : ∀ x, ‖τ x‖ = ‖x‖)
    {q : ℕ} (hτq : ∀ x, τ^[q] x = x) {r ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρr : ρ ≤ r)
    (hq : r < ‖(q : 𝕂)‖) {u₀ : GeneralLinear n 𝕂} (hu₀ : u₀ ∈ normCongruence 𝕂 n r)
    {g : GeneralLinear n 𝕂} (hg : g ∈ normCongruence 𝕂 n (ρ * ‖(q : 𝕂)‖)) :
    ∃ κ ∈ normCongruence 𝕂 n ρ, ∃ u ∈ normCongruence 𝕂 n ρ,
      Matrix.GeneralLinearGroup.map τ u = u ∧
        u₀ * g = κ⁻¹ * (u₀ * u) * Matrix.GeneralLinearGroup.map τ κ := by
  have hr₀ : 0 ≤ r := hρ₀.trans hρr
  set w := ‖(q : 𝕂)‖ with hw
  have hw0 : 0 < w := hr₀.trans_lt hq
  have hqne : (q : 𝕂) ≠ 0 := norm_pos_iff.mp hw0
  have hw1 : w ≤ 1 := IsUltrametricDist.norm_natCast_le_one 𝕂 q
  have hr1 : r < 1 := hq.trans_le hw1
  obtain ⟨t, p, ht, htp, hvt, hvp⟩ := exists_twisted_decomposition τ hτ hτq hqne
  obtain ⟨A, hA⟩ : ∃ A, (u₀ : Mat) = 1 + A := ⟨u₀ - 1, by abel⟩
  obtain ⟨X, hX⟩ : ∃ X, (g : Mat) = 1 + X := ⟨g - 1, by abel⟩
  have bA : Bd r A := fun i j => by simpa [hA] using hu₀ i j
  have bX : Bd (ρ * w) X := fun i j => by simpa [hX] using hg i j
  have hρw : ρ * w ≤ r := (mul_le_of_le_one_right hρ₀ hw1).trans hρr
  have hρw₀ : 0 ≤ ρ * w := mul_nonneg hρ₀ hw0.le
  have hrρ : r * ρ ≤ ρ * w := by nlinarith
  have hρρ : ρ * ρ ≤ ρ * w := by nlinarith
  have bA1 : Bd 1 A := bA.mono hr1.le
  have bB : Bd r (A + X + A * X) :=
    (bA.add (bX.mono hρw)).add ((bA1.mul (bX.mono hρw) zero_le_one hr₀).mono (by simp))
  let U : Mat → Mat := fun Y => Y.map t
  let K : Mat → Mat := fun Y => Y.map p
  let S : Mat → Mat := fun Y => (Y.map p).map τ
  have bU : ∀ {s : ℝ} {Y : Mat}, Bd s Y → Bd (s / w) (U Y) := fun h i j =>
    (hvt _).trans (div_le_div_of_nonneg_right (h i j) hw0.le)
  have bK : ∀ {s : ℝ} {Y : Mat}, Bd s Y → Bd (s / w) (K Y) := fun h i j =>
    (hvp _).trans (div_le_div_of_nonneg_right (h i j) hw0.le)
  have bS : ∀ {s : ℝ} {Y : Mat}, Bd s Y → Bd (s / w) (S Y) := fun h i j =>
    (hτ _).le.trans ((hvp _).trans (div_le_div_of_nonneg_right (h i j) hw0.le))
  have hcan : ρ * w / w = ρ := mul_div_cancel_right₀ _ hw0.ne'
  have bU' : ∀ {Y : Mat}, Bd (ρ * w) Y → Bd ρ (U Y) := fun h => hcan ▸ bU h
  have bK' : ∀ {Y : Mat}, Bd (ρ * w) Y → Bd ρ (K Y) := fun h => hcan ▸ bK h
  have bS' : ∀ {Y : Mat}, Bd (ρ * w) Y → Bd ρ (S Y) := fun h => hcan ▸ bS h
  have sU : ∀ Y Z, U (Y - Z) = U Y - U Z := fun Y Z => by ext i j; simp [U]
  have sK : ∀ Y Z, K (Y - Z) = K Y - K Z := fun Y Z => by ext i j; simp [K]
  have sS : ∀ Y Z, S (Y - Z) = S Y - S Z := fun Y Z => by ext i j; simp [S]
  set B := A + X + A * X with hB
  let Φ : Mat → Mat := fun Y =>
    X + A * X + K Y * B - U Y * S Y - A * U Y - A * S Y - A * (U Y * S Y)
  have hcw : r / w < 1 := (div_lt_one hw0).mpr hq
  have hc₀ : 0 ≤ r / w := div_nonneg hr₀ hw0.le
  obtain ⟨Y, bY, hY⟩ := exists_fixed Φ hc₀ hcw hρw₀
    (fun Y hY => by
      have hUS : Bd (ρ * w) (U Y * S Y) :=
        ((bU' hY).mul (bS' hY) hρ₀ hρ₀).mono hρρ
      have h1 : Bd (ρ * w) (A * X) := (bA1.mul bX zero_le_one hρw₀).mono (by simp)
      have h2 : Bd (ρ * w) (K Y * B) := ((bK' hY).mul bB hρ₀ hr₀).mono (by nlinarith)
      have h3 : Bd (ρ * w) (A * U Y) := ((bA.mul (bU' hY) hr₀ hρ₀)).mono hrρ
      have h4 : Bd (ρ * w) (A * S Y) := ((bA.mul (bS' hY) hr₀ hρ₀)).mono hrρ
      have h5 : Bd (ρ * w) (A * (U Y * S Y)) := (bA1.mul hUS zero_le_one hρw₀).mono (by simp)
      exact (((((bX.add h1).add h2).sub hUS).sub h3).sub h4).sub h5)
    (fun Y Z s hs hY hZ hd => by
      have hsw : 0 ≤ s / w := div_nonneg hs hw0.le
      have e : r / w * s = r * (s / w) := by ring
      have hUS : Bd (r * (s / w)) (U (Y - Z) * S Y + U Z * S (Y - Z)) :=
        (((bU hd).mul ((bS' hY)) hsw hρ₀).mono (by nlinarith)).add
          (((bU' hZ).mul (bS hd) hρ₀ hsw).mono (by nlinarith))
      have hdiff : Φ Y - Φ Z = K (Y - Z) * B - (U (Y - Z) * S Y + U Z * S (Y - Z)) -
          A * U (Y - Z) - A * S (Y - Z) - A * (U (Y - Z) * S Y + U Z * S (Y - Z)) := by
        simp only [Φ]
        rw [sU, sK, sS]
        noncomm_ring
      rw [hdiff, e]
      have h1 : Bd (r * (s / w)) (K (Y - Z) * B) :=
        ((bK hd).mul bB hsw hr₀).mono (le_of_eq (mul_comm _ _))
      have h2 : Bd (r * (s / w)) (A * U (Y - Z)) := bA.mul (bU hd) hr₀ hsw
      have h3 : Bd (r * (s / w)) (A * S (Y - Z)) := bA.mul (bS hd) hr₀ hsw
      have h4 : Bd (r * (s / w)) (A * (U (Y - Z) * S Y + U Z * S (Y - Z))) :=
        (bA1.mul hUS zero_le_one (mul_nonneg hr₀ hsw)).mono (by simp)
      exact (((h1.sub hUS).sub h2).sub h3).sub h4)
  have hlin : U Y + S Y - K Y = Y := by
    ext i j
    simpa [U, S, K] using htp (Y i j)
  have hρ1 : ρ < 1 := hρr.trans_lt hr1
  obtain ⟨κ, hκ⟩ := (bK' bY).isUnit hρ₀ hρ1
  obtain ⟨u, hu⟩ := (bU' bY).isUnit hρ₀ hρ1
  have hσκ : ((Matrix.GeneralLinearGroup.map τ κ : GeneralLinear n 𝕂) : Mat) = 1 + S Y := by
    change (κ : Mat).map τ = _
    rw [hκ]
    ext i j
    simp [S, K, Matrix.one_apply, apply_ite τ]
  refine ⟨κ, fun i j => by simpa [hκ] using bK' bY i j, u,
    fun i j => by simpa [hu] using bU' bY i j, ?_, ?_⟩
  · apply Units.ext
    change (u : Mat).map τ = u
    rw [hu]
    ext i j
    simp [U, ht, Matrix.one_apply, apply_ite τ]
  · rw [mul_assoc, eq_inv_mul_iff_mul_eq]
    apply Units.ext
    simp only [Units.val_mul, hσκ, hκ, hu, hA, hX]
    rw [← sub_eq_zero]
    have : (1 + K Y) * ((1 + A) * (1 + X)) - (1 + A) * (1 + U Y) * (1 + S Y) =
        (X + A * X + K Y * (A + X + A * X) - U Y * S Y - A * U Y - A * S Y - A * (U Y * S Y)) -
          (U Y + S Y - K Y) := by noncomm_ring
    rw [this, hlin]
    exact sub_eq_zero.mpr hY

end Descent

end Langlands.GeneralLinear
