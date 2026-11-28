import Langlands.Global.RankinSelberg.RealCompactDiracCorner
import Langlands.Representation.Archimedean.RealCartanCompactSupport
import Langlands.Representation.Archimedean.BanachModerateGrowth

/-!
# Lipschitz estimates for the Iwasawa coordinates of `GL_n(ℝ)` at the identity

For `g ∈ GL_n(ℝ)` write `g = b κ̂(g)` with `b` upper triangular with positive diagonal and
`κ̂(g) = signedOrthogonalPart g ∈ O(n)`. For complex exponents `s`, the multiplier
`multiplier s g = ∏ₗ b_ll^{s_l}` is the factor of the Library's `extension`:
`extension s φ g = multiplier s g · φ(κ̂(g))`.

The module proves, for the row-sum operator norm, that `‖κ̂(g) - 1‖ ≤ C ‖g - 1‖` for all
`g`, and that `|multiplier s g - 1| ≤ C ‖g - 1‖ ((n + 1) H(g))^q` with
`H(g) = max(1, ‖g‖, ‖g⁻¹‖)` and `q = ∑ₗ |Re s_l|`. Both come from smoothness at the identity
(local Lipschitz bounds) and a crude bound away from it.
-/

noncomputable section

open Matrix Filter Topology
open scoped Matrix.Norms.Operator ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCompactDirac

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open PrincipalSeriesExtension GramFormula

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

/-! ## Row-sum norms and entries -/

theorem abs_entry_le_norm (A : Mat) (i j : Fin n) : |A i j| ≤ ‖A‖ := by
  rw [← Real.norm_eq_abs, Matrix.linfty_opNorm_def]
  have h1 : ‖A i j‖₊ ≤ ∑ k, ‖A i k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖A i k‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)
  have h2 : ∑ k, ‖A i k‖₊ ≤ Finset.univ.sup fun i => ∑ k, ‖A i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

theorem norm_le_of_abs_entry_le {A : Mat} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, |A i j| ≤ c) :
    ‖A‖ ≤ n * c := by
  set c' : NNReal := ⟨c, hc⟩
  have key : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (n : NNReal) * c' := by
    refine Finset.sup_le fun i _ => ?_
    calc ∑ j, ‖A i j‖₊ ≤ ∑ _j : Fin n, c' := Finset.sum_le_sum fun j _ => by
          rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
          exact h i j
      _ = (n : NNReal) * c' := by simp
  rw [Matrix.linfty_opNorm_def]
  have := NNReal.coe_le_coe.2 key
  rwa [NNReal.coe_mul, NNReal.coe_natCast] at this

/-- If the entries of `A` are bounded by `c` times those of `B`, so is the norm. -/
theorem norm_le_of_abs_entry_le_mul {A B : Mat} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) : ‖A‖ ≤ c * ‖B‖ := by
  set c' : NNReal := ⟨c, hc⟩
  have key : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤
      c' * Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ := by
    refine Finset.sup_le fun i _ => ?_
    calc ∑ j, ‖A i j‖₊ ≤ ∑ j, c' * ‖B i j‖₊ := Finset.sum_le_sum fun j _ => by
          rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs,
            Real.norm_eq_abs]
          exact h i j
      _ = c' * ∑ j, ‖B i j‖₊ := by rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          exact Finset.le_sup (f := fun i => ∑ j, ‖B i j‖₊) (Finset.mem_univ i)
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  have := NNReal.coe_le_coe.2 key
  rwa [NNReal.coe_mul] at this

theorem norm_orthogonal_le (κ : O) : ‖(κ : Mat)‖ ≤ n := by
  have h := norm_le_of_abs_entry_le (A := (κ : Mat)) zero_le_one fun i j => by
    have := entry_norm_bound_of_unitary κ.2 i j
    rwa [Real.norm_eq_abs] at this
  simpa using h

theorem norm_one_le : ‖(1 : Mat)‖ ≤ n := by
  have h := norm_le_of_abs_entry_le (A := (1 : Mat)) zero_le_one fun i j => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  simpa using h

/-! ## The multiplier of the extension -/

/-- The factor `∏ₗ b_ll^{s_l}` of the extension, for `g = b κ̂(g)` with `b` upper triangular
with positive diagonal. -/
def multiplier (s : Fin n → ℂ) (g : G) : ℂ := gramExpression s 1 (complexify (g : Mat))

theorem extension_eq_multiplier (s : Fin n → ℂ) (φ : O → ℂ) (g : G) :
    extension s φ g = multiplier s g * φ (signedOrthogonalPart g) := rfl

theorem multiplier_eq (s : Fin n → ℂ) {g : G} {b κ : Mat} (hb : b.IsUpperTriangular)
    (hd : ∀ l, b l l ≠ 0) (hκ : κ ∈ O) (hg : (g : Mat) = b * κ) :
    multiplier s g = ∏ l, ((|b l l| : ℝ) : ℂ) ^ s l := by
  have h := extension_eq s (fun _ => (1 : ℂ)) hb hd hκ hg
  rw [extension_eq_multiplier, mul_one, mul_one] at h
  exact h

theorem multiplier_one (s : Fin n → ℂ) : multiplier s (1 : G) = 1 := by
  have h := extension_unitary s (fun _ => (1 : ℂ)) 1
  rw [extension_eq_multiplier, mul_one, map_one] at h
  exact h

theorem continuous_multiplier (s : Fin n → ℂ) : Continuous (multiplier (n := n) s) :=
  (contDiffOn_gramExpression s 1).continuousOn.comp_continuous Units.continuous_val
    fun g => g.isUnit

theorem signedOrthogonal_one : signedOrthogonal (1 : Mat) = 1 := by
  have h := signedOrthogonal_mul (b := (1 : Mat)) (κ := (1 : Mat)) Matrix.blockTriangular_one
    (fun l => by simp) (by simp)
  rw [Matrix.one_mul] at h
  rw [h, Matrix.mul_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp [signReal]

/-! ## Local Lipschitz bounds at the identity -/

theorem exists_eventually_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Mat → E} (hf : ContDiffAt ℝ 1 f 1) :
    ∃ K : ℝ, ∀ᶠ y in 𝓝 (1 : Mat), ‖f y - f 1‖ ≤ K * ‖y - 1‖ := by
  obtain ⟨K, t, ht, hL⟩ := hf.exists_lipschitzOnWith
  refine ⟨K, ?_⟩
  filter_upwards [ht] with y hy
  have := hL.dist_le_mul y hy 1 (mem_of_mem_nhds ht)
  simpa [dist_eq_norm] using this

theorem gram_one_pos (l : ℕ) : 0 < gram l (1 : Mat) := by
  have := gram_pos (1 : G) l
  simpa using this

theorem contDiffAt_signedOrthogonal_entry (i j : Fin n) :
    ContDiffAt ℝ 1 (fun y : Mat => signedOrthogonal y i j) 1 := by
  have hg : ∀ l : ℕ, ContDiffAt ℝ 1 (fun y : Mat => (Real.sqrt (gram l y))⁻¹) 1 := by
    intro l
    have h0 : gram l (1 : Mat) ≠ 0 := (gram_one_pos l).ne'
    refine ContDiffAt.inv (((contDiff_gram l).contDiffAt.of_le (by simp)).sqrt h0) ?_
    exact (Real.sqrt_pos.2 (gram_one_pos l)).ne'
  simp only [signedOrthogonal, Matrix.of_apply]
  exact (((contDiff_gramColumn i j).contDiffAt.of_le (by simp)).mul (hg _)).mul (hg _)

theorem contDiffAt_multiplier (s : Fin n → ℂ) :
    ContDiffAt ℝ 1 (fun y : Mat => gramExpression s 1 (complexify y)) 1 := by
  have h := contDiffOn_gramExpression s 1
  exact ((h.contDiffAt (isOpen_setOf_isUnit_matrix.mem_nhds isUnit_one)).of_le (by simp))

/-! ## The signed orthogonal part near the identity -/

/-- **Lipschitz bound for `κ̂` at the identity.** -/
theorem exists_norm_signedOrthogonalPart_sub_one_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G,
      ‖((signedOrthogonalPart g : O) : Mat) - 1‖ ≤ C * ‖(g : Mat) - 1‖ := by
  have hent : ∀ i j : Fin n, ∃ K : ℝ, ∀ᶠ y in 𝓝 (1 : Mat),
      ‖signedOrthogonal y i j - signedOrthogonal (1 : Mat) i j‖ ≤ K * ‖y - 1‖ :=
    fun i j => exists_eventually_lipschitz (contDiffAt_signedOrthogonal_entry i j)
  choose K hK using hent
  have hall : ∀ᶠ y in 𝓝 (1 : Mat), ∀ i j,
      ‖signedOrthogonal y i j - signedOrthogonal (1 : Mat) i j‖ ≤ K i j * ‖y - 1‖ :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hK i j
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hall
  set K₀ : ℝ := ∑ i, ∑ j, |K i j| with hK₀
  have hK₀nn : 0 ≤ K₀ := by positivity
  have hKle : ∀ i j, K i j ≤ K₀ := fun i j => by
    calc K i j ≤ |K i j| := le_abs_self _
      _ ≤ ∑ j, |K i j| := Finset.single_le_sum (f := fun j => |K i j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ K₀ := Finset.single_le_sum (f := fun i => ∑ j, |K i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  refine ⟨max (n * K₀) (2 * n / ε), le_max_of_le_left (by positivity), fun g => ?_⟩
  have hgn : 0 ≤ ‖(g : Mat) - 1‖ := norm_nonneg _
  by_cases hg : ‖(g : Mat) - 1‖ < ε
  · have hb := hball (y := (g : Mat)) (by rwa [dist_eq_norm])
    have hentry : ∀ i j, |(((signedOrthogonalPart g : O) : Mat) - 1) i j| ≤ K₀ * ‖(g : Mat) - 1‖ := by
      intro i j
      have := hb i j
      rw [signedOrthogonal_one, Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_right (hKle i j) hgn)
    calc _ ≤ n * (K₀ * ‖(g : Mat) - 1‖) := norm_le_of_abs_entry_le (by positivity) hentry
      _ = (n * K₀) * ‖(g : Mat) - 1‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hgn
  · push Not at hg
    have h1 : ‖((signedOrthogonalPart g : O) : Mat) - 1‖ ≤ 2 * n := by
      calc _ ≤ ‖((signedOrthogonalPart g : O) : Mat)‖ + ‖(1 : Mat)‖ := norm_sub_le _ _
        _ ≤ n + n := add_le_add (norm_orthogonal_le _) norm_one_le
        _ = 2 * n := by ring
    have h2 : 2 * (n : ℝ) ≤ 2 * n / ε * ‖(g : Mat) - 1‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]
      exact mul_le_mul_of_nonneg_left hg (by positivity)
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hgn))


/-! ## Growth and Lipschitz bound of the multiplier -/

theorem rpow_le_of_le_of_inv_le {x M r : ℝ} (hx : 0 < x) (h1 : x ≤ M) (h2 : x⁻¹ ≤ M) :
    x ^ r ≤ M ^ |r| := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr]
    exact Real.rpow_le_rpow hx.le h1 hr
  · rw [abs_of_nonpos hr]
    have hx' : x ^ r = x⁻¹ ^ (-r) := by
      rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, neg_neg]
    rw [hx']
    exact Real.rpow_le_rpow (inv_pos.2 hx).le h2 (by linarith)

/-- The exponent `∑ₗ |Re s_l|` of the polynomial growth of the multiplier. -/
def growthExponent (s : Fin n → ℂ) : ℝ := ∑ l, |(s l).re|

theorem growthExponent_nonneg (s : Fin n → ℂ) : 0 ≤ growthExponent s :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The base `(n + 1) H(g)` of the polynomial growth of the multiplier. -/
def heightBase (g : G) : ℝ := ((n : ℝ) + 1) * unitHeight g

theorem one_le_heightBase (g : G) : 1 ≤ heightBase g := by
  unfold heightBase
  have h1 := one_le_unitHeight g
  have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  nlinarith

theorem one_le_heightBase_rpow (s : Fin n → ℂ) (g : G) :
    1 ≤ heightBase g ^ growthExponent s :=
  Real.one_le_rpow (one_le_heightBase g) (growthExponent_nonneg s)

/-- **Polynomial growth of the multiplier.** -/
theorem norm_multiplier_le (s : Fin n → ℂ) (g : G) :
    ‖multiplier s g‖ ≤ heightBase g ^ growthExponent s := by
  obtain ⟨a, u, k, hk, hg⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  set B : G := (Iwasawa.diagonalUnits a : G) * (u : G) with hBdef
  set b : Mat := Matrix.diagonal (fun l => (a l : ℝ)) * ((u : G) : Mat) with hbdef
  have hbB : (B : Mat) = b := by
    rw [hBdef, hbdef, Units.val_mul, Iwasawa.diagonalUnits_val]
  have hb : b.IsUpperTriangular := isUpperTriangular_diagonal_mul a u
  have hbd : ∀ l, b l l = a l := diagonal_mul_apply_self a u
  have hd : ∀ l, b l l ≠ 0 := fun l => by rw [hbd]; exact (a l).ne_zero
  have hgb : (g : Mat) = b * (k : Mat) := by
    rw [hg, ← hbB, ← Units.val_mul]
  rw [multiplier_eq s hb hd hk hgb]
  have hkT : (k : Mat) * (k : Mat)ᵀ = 1 := mul_transpose_eq_one_of_mem hk
  have hkO : (k : Mat) ∈ O := hk
  have hkTk : (k : Mat)ᵀ * (k : Mat) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hkO
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hkTO : (k : Mat)ᵀ ∈ O := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    exact hkTk
  have hH0 : 0 ≤ unitHeight g := zero_le_one.trans (one_le_unitHeight g)
  have hH : unitHeight g ≤ heightBase g / ((n : ℝ) + 1) := by
    rw [heightBase, mul_div_cancel_left₀ _ (by positivity)]
  -- upper bound for the diagonal entries
  have hup : ∀ l, |(a l : ℝ)| ≤ heightBase g := by
    intro l
    have hbg : b = (g : Mat) * (k : Mat)ᵀ := by
      rw [hgb, Matrix.mul_assoc, hkT, Matrix.mul_one]
    calc |(a l : ℝ)| = |b l l| := by rw [hbd]
      _ ≤ ‖b‖ := abs_entry_le_norm b l l
      _ ≤ ‖(g : Mat)‖ * ‖(k : Mat)ᵀ‖ := by rw [hbg]; exact Matrix.linfty_opNorm_mul _ _
      _ ≤ unitHeight g * n := mul_le_mul (norm_val_le_unitHeight g)
          (norm_orthogonal_le ⟨_, hkTO⟩) (norm_nonneg _) hH0
      _ ≤ heightBase g := by
          unfold heightBase
          have := one_le_unitHeight g
          nlinarith
  -- upper bound for the inverses of the diagonal entries
  have hlow : ∀ l, |(a l : ℝ)|⁻¹ ≤ heightBase g := by
    intro l
    have hBinv : (B⁻¹ : G) = k * g⁻¹ := by
      rw [hg, _root_.mul_inv_rev B k, mul_inv_cancel_left]
    have hu' : ((u⁻¹ : upperUnipotent n ℝ) : G) ∈ upperUnipotent n ℝ := (u⁻¹).2
    have hentry : (((B⁻¹ : G) : Mat)) l l = ((a l : ℝ))⁻¹ := by
      rw [hBdef, _root_.mul_inv_rev, Units.val_mul, ← map_inv, Iwasawa.diagonalUnits_val,
        Matrix.mul_diagonal]
      have h1 : (((u : G)⁻¹ : G) : Mat) l l = 1 := by
        have := hu'.2 l
        rwa [Subgroup.coe_inv] at this
      rw [h1, one_mul, Pi.inv_apply, Units.val_inv_eq_inv_val]
    calc |(a l : ℝ)|⁻¹ = |(((B⁻¹ : G) : Mat)) l l| := by rw [hentry, abs_inv]
      _ ≤ ‖(((B⁻¹ : G) : Mat))‖ := abs_entry_le_norm _ l l
      _ = ‖(k : Mat) * ((g⁻¹ : G) : Mat)‖ := by rw [hBinv, Units.val_mul]
      _ ≤ ‖(k : Mat)‖ * ‖((g⁻¹ : G) : Mat)‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ n * unitHeight g := mul_le_mul (norm_orthogonal_le ⟨_, hkO⟩)
          (norm_inv_le_unitHeight g) (norm_nonneg _) (by positivity)
      _ ≤ heightBase g := by
          unfold heightBase
          have := one_le_unitHeight g
          nlinarith
  rw [norm_prod, growthExponent, Real.rpow_sum_of_pos (by linarith [one_le_heightBase g])]
  gcongr with l _
  have hpos : 0 < |b l l| := abs_pos.2 (hd l)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  rw [hbd] at hpos ⊢
  exact rpow_le_of_le_of_inv_le hpos (hup l) (hlow l)

/-- **Lipschitz bound for the multiplier at the identity**, with polynomial growth away from
it. -/
theorem exists_norm_multiplier_sub_one_le (s : Fin n → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ‖multiplier s g - 1‖ ≤
      C * ‖(g : Mat) - 1‖ * heightBase g ^ growthExponent s := by
  obtain ⟨K, hK⟩ := exists_eventually_lipschitz (contDiffAt_multiplier s)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hK
  have h1 : gramExpression s 1 (complexify (1 : Mat)) = 1 := multiplier_one s
  refine ⟨|K| + 2 / ε, by positivity, fun g => ?_⟩
  have hP := one_le_heightBase_rpow s g
  have hgn : 0 ≤ ‖(g : Mat) - 1‖ := norm_nonneg _
  by_cases hg : ‖(g : Mat) - 1‖ < ε
  · have hb := hball (y := (g : Mat)) (by rwa [dist_eq_norm])
    rw [h1] at hb
    change ‖multiplier s g - 1‖ ≤ K * ‖(g : Mat) - 1‖ at hb
    calc ‖multiplier s g - 1‖ ≤ |K| * ‖(g : Mat) - 1‖ :=
          hb.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hgn)
      _ ≤ (|K| + 2 / ε) * ‖(g : Mat) - 1‖ * 1 := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (by linarith [div_pos two_pos hε]) hgn
      _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)
  · push Not at hg
    have hm := norm_multiplier_le s g
    calc ‖multiplier s g - 1‖ ≤ ‖multiplier s g‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ heightBase g ^ growthExponent s + heightBase g ^ growthExponent s := by
          rw [norm_one]; exact add_le_add hm hP
      _ = 2 / ε * ε * heightBase g ^ growthExponent s := by
          field_simp
          ring
      _ ≤ 2 / ε * ‖(g : Mat) - 1‖ * heightBase g ^ growthExponent s := by
          gcongr
      _ ≤ _ := by
          gcongr
          linarith [abs_nonneg K]


end Langlands.Global.RankinSelbergGlobal.RealCompactDirac
