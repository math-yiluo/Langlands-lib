import Langlands.Global.RankinSelberg.RealCompactDifferences
import Langlands.Global.RankinSelberg.RealPrincipalSeriesHeight
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Representation.Archimedean.KIntegralInvariance

/-!
# Compact right differences of real principal-series sections from right derivatives

On the compact picture of a real principal series, iterated right differences are controlled by
uniform bounds of iterated right derivatives in the elementary matrix directions.
-/

noncomputable section

open scoped Classical Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCompactDerivativeDifferences

open Langlands.Archimedean (principalSeries realPositionCharacter unitaryCompact matrixModel
  rightDerivative rightDerivative_eq_fderiv rightDerivative_add rightDerivative_smul
  contMDiff_rightDerivative unitsExtension unitsExtension_val differentiableAt_unitsExtension)
open Langlands.LocalFactor.Archimedean (RealBlock)
open RealLocalWhittaker (iteratedRightDerivative)

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "UC" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "I" => matrixModel ℝ (r + 1)
local notation "Idx" => Fin (r + 1) × Fin (r + 1)

/-- The elementary matrix with one entry `1`. -/
def elem (ab : Fin (r + 1) × Fin (r + 1)) : M := Matrix.single ab.1 ab.2 1

/-- The matrix word of a list of elementary indices. -/
def word (w : List (Fin (r + 1) × Fin (r + 1))) : List M := w.map elem

/-- The sum of the absolute values of the entries. -/
def entryNorm (Y : M) : ℝ := ∑ ab : Idx, ‖Y ab.1 ab.2‖

theorem entryNorm_nonneg (Y : M) : 0 ≤ entryNorm Y :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The product of the entry norms of the letters of a word. -/
def wordNorm (Ys : List M) : ℝ := (Ys.map entryNorm).prod

theorem wordNorm_nonneg (Ys : List M) : 0 ≤ wordNorm Ys := by
  induction Ys with
  | nil => exact zero_le_one
  | cons Y Ys ih => exact mul_nonneg (entryNorm_nonneg Y) ih

/-- A uniform bound on the compact group for all elementary words of length at most `m`. -/
def WordBound (m : ℕ) (u : G → ℂ) (R : ℝ) : Prop :=
  ∀ w : List Idx, w.length ≤ m → ∀ x : UC,
    ‖iteratedRightDerivative r (word w) u (Unitary.toUnits x)‖ ≤ R

theorem WordBound.mono {m m' : ℕ} {u : G → ℂ} {R R' : ℝ} (h : WordBound m u R) (hm : m' ≤ m)
    (hR : R ≤ R') : WordBound m' u R' :=
  fun w hw x => (h w (hw.trans hm) x).trans hR

theorem WordBound.nonneg {m : ℕ} {u : G → ℂ} {R : ℝ} (h : WordBound m u R) : 0 ≤ R :=
  (norm_nonneg _).trans (h [] (Nat.zero_le m) 1)

/-! ## Linear algebra of right derivatives -/

private theorem matrix_eq_sum (Y : M) : Y = ∑ ab : Idx, Y ab.1 ab.2 • elem ab := by
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  simp only [elem, Matrix.smul_single, smul_eq_mul, mul_one]

/-- Right derivatives are real-linear in the direction. -/
theorem rightDerivative_eq_sum {u : G → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) ∞ u) (Y : M) (g : G) :
    rightDerivative I Y u g = ∑ ab : Idx, (Y ab.1 ab.2 : ℂ) * rightDerivative I (elem ab) u g := by
  rw [rightDerivative_eq_fderiv hu]
  conv_lhs => rw [matrix_eq_sum Y]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [rightDerivative_eq_fderiv hu, Matrix.mul_smul, map_smul, Complex.real_smul]

theorem iter_cons (X : M) (Xs : List M) (u : G → ℂ) :
    iteratedRightDerivative r (X :: Xs) u = rightDerivative I X (iteratedRightDerivative r Xs u) :=
  rfl

theorem iter_append_singleton (Xs : List M) (X : M) (u : G → ℂ) :
    iteratedRightDerivative r (Xs ++ [X]) u =
      iteratedRightDerivative r Xs (rightDerivative I X u) := by
  simp [iteratedRightDerivative, List.foldr_append]

theorem contMDiff_iter {u : G → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) ∞ u) (Xs : List M) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (iteratedRightDerivative r Xs u) :=
  RealUniformWhittaker.contMDiff_iteratedRightDerivative hu Xs

theorem iter_sum {ι : Type*} (s : Finset ι) {u : ι → G → ℂ}
    (hu : ∀ i, ContMDiff I 𝓘(ℝ, ℂ) ∞ (u i)) (c : ι → ℂ) (Xs : List M) :
    iteratedRightDerivative r Xs (∑ i ∈ s, c i • u i) =
      ∑ i ∈ s, c i • iteratedRightDerivative r Xs (u i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact RealUniformWhittaker.iteratedRightDerivative_zero Xs
  | @insert i s hi ih =>
    have hs : ContMDiff I 𝓘(ℝ, ℂ) ∞ (∑ j ∈ s, c j • u j) := by
      have : ∀ t : Finset ι, ContMDiff I 𝓘(ℝ, ℂ) ∞ (∑ j ∈ t, c j • u j) := by
        intro t
        induction t using Finset.induction_on with
        | empty => simp only [Finset.sum_empty]; exact contMDiff_const
        | @insert j t hj ihj =>
          rw [Finset.sum_insert hj]
          exact (((c j • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp
            (hu j)).add ihj
      exact this s
    have hc : ContMDiff I 𝓘(ℝ, ℂ) ∞ (c i • u i) :=
      ((c i • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp (hu i)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      RealUniformWhittaker.iteratedRightDerivative_add hc hs,
      RealUniformWhittaker.iteratedRightDerivative_smul (hu i), ih]

/-- Expanding the innermost direction of a word in elementary matrices. -/
theorem iter_append_eq_sum {u : G → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) ∞ u) (Xs : List M) (Y : M) :
    iteratedRightDerivative r (Xs ++ [Y]) u =
      ∑ ab : Idx, (Y ab.1 ab.2 : ℂ) • iteratedRightDerivative r (Xs ++ [elem ab]) u := by
  have h : rightDerivative I Y u = ∑ ab : Idx, (Y ab.1 ab.2 : ℂ) • rightDerivative I (elem ab) u := by
    funext g
    rw [rightDerivative_eq_sum hu, Finset.sum_apply]
    rfl
  rw [iter_append_singleton, h, iter_sum _ (fun ab => contMDiff_rightDerivative hu (elem ab))]
  simp only [iter_append_singleton]

/-! ## Bounds for arbitrary words -/

/-- A word bound for elementary words controls every word of the same length, with the product
of the entry norms of its letters. -/
theorem norm_iter_le {u : G → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) ∞ u) (Ys : List M) {R : ℝ}
    (h : WordBound Ys.length u R) (x : UC) :
    ‖iteratedRightDerivative r Ys u (Unitary.toUnits x)‖ ≤ wordNorm Ys * R := by
  induction Ys using List.reverseRecOn generalizing u with
  | nil => simpa [wordNorm, word] using h [] le_rfl x
  | append_singleton Ys Y ih =>
    rw [iter_append_singleton]
    have hsum : rightDerivative I Y u =
        ∑ ab : Idx, (Y ab.1 ab.2 : ℂ) • rightDerivative I (elem ab) u := by
      funext g
      rw [rightDerivative_eq_sum hu, Finset.sum_apply]
      rfl
    rw [hsum, iter_sum _ (fun ab => contMDiff_rightDerivative hu (elem ab)), Finset.sum_apply]
    have hb (ab : Idx) : ‖iteratedRightDerivative r Ys (rightDerivative I (elem ab) u)
        (Unitary.toUnits x)‖ ≤ wordNorm Ys * R := by
      refine ih (contMDiff_rightDerivative hu (elem ab)) (fun w hw y => ?_)
      have hw' := h (w ++ [ab]) (by simp; omega) y
      simpa [word, iter_append_singleton] using hw'
    have hR : 0 ≤ R := h.nonneg
    calc
      _ ≤ ∑ ab : Idx, ‖(Y ab.1 ab.2 : ℂ) • iteratedRightDerivative r Ys
            (rightDerivative I (elem ab) u) (Unitary.toUnits x)‖ := by
        simp only [Pi.smul_apply]
        exact norm_sum_le _ _
      _ ≤ ∑ ab : Idx, ‖Y ab.1 ab.2‖ * (wordNorm Ys * R) := by
        refine Finset.sum_le_sum fun ab _ => ?_
        rw [norm_smul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (hb ab) (norm_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul]
        simp only [wordNorm, List.map_append, List.prod_append, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one, entryNorm]
        ring

theorem iter_append (Ws Ys : List M) (u : G → ℂ) :
    iteratedRightDerivative r (Ws ++ Ys) u =
      iteratedRightDerivative r Ws (iteratedRightDerivative r Ys u) := by
  simp [iteratedRightDerivative, List.foldr_append]

theorem iter_sub {u v : G → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) ∞ u) (hv : ContMDiff I 𝓘(ℝ, ℂ) ∞ v)
    (Xs : List M) :
    iteratedRightDerivative r Xs (u - v) =
      iteratedRightDerivative r Xs u - iteratedRightDerivative r Xs v := by
  have hv' : ContMDiff I 𝓘(ℝ, ℂ) ∞ ((-1 : ℂ) • v) :=
    (((-1 : ℂ) • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hv
  have e : u - v = u + (-1 : ℂ) • v := by funext g; simp [sub_eq_add_neg]
  rw [e, RealUniformWhittaker.iteratedRightDerivative_add hu hv',
    RealUniformWhittaker.iteratedRightDerivative_smul hv]
  funext g
  simp [sub_eq_add_neg]

private theorem rightDerivative_sub_direction {u : G → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) ∞ u)
    (Y Z : M) :
    rightDerivative I Y u - rightDerivative I Z u = rightDerivative I (Y - Z) u := by
  funext g
  rw [Pi.sub_apply, rightDerivative_eq_sum hu Y, rightDerivative_eq_sum hu Z,
    rightDerivative_eq_sum hu (Y - Z), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Matrix.sub_apply, Complex.ofReal_sub, sub_mul]

/-- Changing the letters of a word changes the iterated derivative by at most the size of the
changes, measured in entry norms. -/
theorem norm_iter_sub_le {u : G → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) ∞ u) {δ β : ℝ} (hβ : 1 ≤ β)
    (x : UC) : ∀ (Ws Ys Zs : List M),
    List.Forall₂ (fun Y Z => entryNorm (Y - Z) ≤ δ ∧ entryNorm Y ≤ β ∧ entryNorm Z ≤ β) Ys Zs →
    ∀ {R : ℝ}, WordBound (Ws.length + Ys.length) u R →
    ‖iteratedRightDerivative r (Ws ++ Ys) u (Unitary.toUnits x) -
        iteratedRightDerivative r (Ws ++ Zs) u (Unitary.toUnits x)‖ ≤
      wordNorm Ws * (Ys.length * δ * β ^ Ys.length) * R := by
  intro Ws Ys Zs hYZ
  induction hYZ generalizing Ws with
  | nil => intro R _; simp
  | @cons Y Z Ys Zs hc hrest ih =>
    intro R h
    have hR : 0 ≤ R := h.nonneg
    have hδ : 0 ≤ δ := (entryNorm_nonneg _).trans hc.1
    have hβ0 : 0 ≤ β := zero_le_one.trans hβ
    have hlen : Ys.length = Zs.length := hrest.length_eq
    have hYs : wordNorm Ys ≤ β ^ Ys.length := by
      clear ih h hlen
      induction hrest with
      | nil => simp [wordNorm]
      | @cons Y' Z' Ys' Zs' hc' _ ih' =>
        simp only [wordNorm, List.map_cons, List.prod_cons, List.length_cons, pow_succ'] at ih' ⊢
        exact mul_le_mul hc'.2.1 ih' (wordNorm_nonneg Ys') hβ0
    -- split the change of the first letter from the change of the tail
    have hsplit : iteratedRightDerivative r (Ws ++ Y :: Ys) u - iteratedRightDerivative r (Ws ++ Z :: Zs) u =
        iteratedRightDerivative r (Ws ++ (Y - Z) :: Ys) u +
          (iteratedRightDerivative r ((Ws ++ [Z]) ++ Ys) u -
            iteratedRightDerivative r ((Ws ++ [Z]) ++ Zs) u) := by
      have hv := contMDiff_iter hu Ys
      have e1 : iteratedRightDerivative r (Ws ++ Y :: Ys) u - iteratedRightDerivative r (Ws ++ Z :: Ys) u =
          iteratedRightDerivative r (Ws ++ (Y - Z) :: Ys) u := by
        rw [iter_append, iter_append, iter_append, iter_cons, iter_cons, iter_cons,
          ← iter_sub (contMDiff_rightDerivative hv Y) (contMDiff_rightDerivative hv Z),
          rightDerivative_sub_direction hv]
      have e2 : (Ws ++ [Z]) ++ Ys = Ws ++ Z :: Ys := by simp
      have e3 : (Ws ++ [Z]) ++ Zs = Ws ++ Z :: Zs := by simp
      rw [e2, e3, ← e1]
      abel
    have h1 : ‖iteratedRightDerivative r (Ws ++ (Y - Z) :: Ys) u (Unitary.toUnits x)‖ ≤
        wordNorm Ws * (δ * β ^ Ys.length) * R := by
      have hb := norm_iter_le hu (Ws ++ (Y - Z) :: Ys) (R := R) (by simpa using h) x
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_right _ hR
      simp only [wordNorm, List.map_append, List.prod_append, List.map_cons, List.prod_cons] at hYs ⊢
      exact mul_le_mul_of_nonneg_left (mul_le_mul hc.1 hYs (wordNorm_nonneg Ys) hδ)
        (wordNorm_nonneg Ws)
    have h2 := ih (Ws ++ [Z]) (R := R) (by
      apply h.mono _ le_rfl
      simp; omega)
    have hWZ : wordNorm (Ws ++ [Z]) ≤ wordNorm Ws * β := by
      simp only [wordNorm, List.map_append, List.prod_append, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      exact mul_le_mul_of_nonneg_left hc.2.2 (wordNorm_nonneg Ws)
    have hsplit' := congrFun hsplit (Unitary.toUnits x)
    simp only [Pi.sub_apply, Pi.add_apply] at hsplit'
    rw [hsplit']
    calc
      _ ≤ ‖iteratedRightDerivative r (Ws ++ (Y - Z) :: Ys) u (Unitary.toUnits x)‖ +
          ‖iteratedRightDerivative r ((Ws ++ [Z]) ++ Ys) u (Unitary.toUnits x) -
            iteratedRightDerivative r ((Ws ++ [Z]) ++ Zs) u (Unitary.toUnits x)‖ := norm_add_le _ _
      _ ≤ wordNorm Ws * (δ * β ^ Ys.length) * R +
          wordNorm (Ws ++ [Z]) * (Ys.length * δ * β ^ Ys.length) * R := add_le_add h1 h2
      _ ≤ wordNorm Ws * (δ * β ^ Ys.length) * R +
          (wordNorm Ws * β) * (Ys.length * δ * β ^ Ys.length) * R := by
        gcongr
      _ ≤ _ := by
        simp only [List.length_cons, Nat.cast_succ, pow_succ]
        have hW := wordNorm_nonneg Ws
        have hp : 0 ≤ β ^ Ys.length := pow_nonneg hβ0 _
        nlinarith [mul_nonneg (mul_nonneg hW hδ) (mul_nonneg hp hR),
          mul_nonneg (mul_nonneg (mul_nonneg hW hδ) (mul_nonneg hp hR)) (sub_nonneg.mpr hβ)]

/-- Right translation commutes with right derivatives after conjugating the directions. -/
theorem iter_translate {u : G → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) ∞ u) (h : G) (Ys : List M) :
    iteratedRightDerivative r Ys (fun g => u (g * h)) =
      fun g => iteratedRightDerivative r
        (Ys.map fun Y => ((h⁻¹ : G) : M) * Y * (h : M)) u (g * h) := by
  induction Ys with
  | nil => rfl
  | cons Y Ys ih =>
    rw [iter_cons, ih]
    funext g
    have hv := contMDiff_iter hu (Ys.map fun Y => ((h⁻¹ : G) : M) * Y * (h : M))
    have e := Langlands.Archimedean.KIntegralInvariance.rightDerivative_mul_eq hv h g
      (((h⁻¹ : G) : M) * Y * (h : M))
    have hY : (h : M) * (((h⁻¹ : G) : M) * Y * (h : M)) * ((h⁻¹ : G) : M) = Y := by
      have h1 : (h : M) * ((h⁻¹ : G) : M) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have h2 : ((h⁻¹ : G) : M) * (h : M) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc
        _ = ((h : M) * ((h⁻¹ : G) : M)) * Y * ((h : M) * ((h⁻¹ : G) : M)) := by
          simp only [Matrix.mul_assoc]
        _ = Y := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    rw [hY] at e
    rw [List.map_cons, iter_cons]
    exact e.symm

/-! ## One right difference -/

private theorem norm_entry_le_opNorm (A : M) (i j : Fin (r + 1)) : ‖A i j‖ ≤ ‖A‖ := by
  change (‖A i j‖₊ : ℝ) ≤ (‖A‖₊ : ℝ)
  rw [NNReal.coe_le_coe, Matrix.linfty_opNNNorm_def]
  exact (Finset.single_le_sum (f := fun l => ‖A i l‖₊) (fun _ _ => bot_le)
    (Finset.mem_univ j)).trans (Finset.le_sup (f := fun l => ∑ j, ‖A l j‖₊) (Finset.mem_univ i))

private theorem opNorm_unitary_le (x : UC) : ‖(x : M)‖ ≤ (r + 1 : ℝ) := by
  change (‖(x : M)‖₊ : ℝ) ≤ _
  rw [Matrix.linfty_opNNNorm_def]
  have h : (Finset.univ.sup fun i => ∑ j, ‖(x : M) i j‖₊) ≤ ((r + 1 : ℕ) : NNReal) := by
    refine Finset.sup_le fun i _ => ?_
    calc
      (∑ j, ‖(x : M) i j‖₊) ≤ ∑ _j : Fin (r + 1), (1 : NNReal) :=
        Finset.sum_le_sum fun j _ => by
          have := entry_norm_bound_of_unitary x.2 i j
          exact_mod_cast this
      _ = _ := by simp
  have h' := NNReal.coe_le_coe.mpr h
  simpa using h'

private theorem height_le_opNorms (g : G) :
    realMatrixHeight g ≤ (r + 1 : ℝ) ^ 2 * (‖(g : M)‖ ^ 2 + ‖((g⁻¹ : G) : M)‖ ^ 2) := by
  unfold realMatrixHeight
  calc
    _ ≤ ∑ _i : Fin (r + 1), ∑ _j : Fin (r + 1), (‖(g : M)‖ ^ 2 + ‖((g⁻¹ : G) : M)‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) (norm_entry_le_opNorm _ i j) 2)
          (pow_le_pow_left₀ (norm_nonneg _) (norm_entry_le_opNorm _ i j) 2)
    _ = _ := by simp; ring

/-- One compact right difference of a principal-series function is bounded by its first right
derivatives in the elementary directions, uniformly on the compact group. -/
theorem exists_oneStep (ds : List RealBlock) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : G → ℂ), u ∈ principalSeries ℝ (r + 1) (realPositionCharacter ds) →
      ∀ R : ℝ, WordBound 1 u R → ∀ x k : UC,
        ‖u (Unitary.toUnits (x * k)) - u (Unitary.toUnits x)‖ ≤ C * ‖(k : M) - 1‖ * R := by
  obtain ⟨A, N, hA, hH⟩ :=
    RealPrincipalSeries.realPrincipalSeriesHeight (r + 1) (Nat.succ_pos r) ds
  let m : ℝ := r + 1
  have hm : 0 ≤ m := by positivity
  let H₀ : ℝ := 8 * m ^ 4
  let C₁ : ℝ := m ^ 2 * 2 * (A * H₀ ^ N)
  refine ⟨max 4 C₁, by positivity, fun u hu R hR x k => ?_⟩
  have hR0 : 0 ≤ R := hR.nonneg
  have hval (y : UC) : ‖u (Unitary.toUnits y)‖ ≤ R := by
    simpa [word, iteratedRightDerivative] using hR [] (Nat.zero_le 1) y
  by_cases hk : ‖(k : M) - 1‖ < 1 / 2
  · -- the straight path from `x` to `x k`
    let z : ℝ → M := fun t => -(t • ((k : M) - 1))
    have hz (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖z t‖ ≤ 1 / 2 := by
      simp only [z, norm_neg, norm_smul, Real.norm_of_nonneg ht.1]
      nlinarith [norm_nonneg ((k : M) - 1), ht.2]
    have hz1 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖z t‖ < 1 :=
      (hz t ht).trans_lt (by norm_num)
    let γ : ℝ → M := fun t => (x : M) * (1 + t • ((k : M) - 1))
    let F := unitsExtension u
    have hγunit (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : IsUnit (γ t) := by
      have h1 : IsUnit (1 + t • ((k : M) - 1)) := by
        have := isUnit_one_sub_of_norm_lt_one (hz1 t ht)
        simpa [z, sub_eq_add_neg] using this
      exact (Units.isUnit (Unitary.toUnits x)).mul h1
    have hderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
        HasDerivWithinAt (fun t => F (γ t)) (fderiv ℝ F (γ t) ((x : M) * ((k : M) - 1)))
          (Set.Icc 0 1) t := by
      have hF : HasFDerivAt F (fderiv ℝ F (γ t)) (γ t) :=
        (differentiableAt_unitsExtension hu.1 (hγunit t ht)).hasFDerivAt
      have hγ : HasDerivAt γ ((x : M) * ((k : M) - 1)) t := by
        have h0 : HasDerivAt (fun t : ℝ => t • ((k : M) - 1)) ((k : M) - 1) t := by
          simpa using (hasDerivAt_id t).smul_const ((k : M) - 1)
        have h1 := (h0.const_add 1).const_mul (x : M)
        simpa [γ] using h1
      exact (hF.comp_hasDerivAt t hγ).hasDerivWithinAt
    have hbound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
        ‖fderiv ℝ F (γ t) ((x : M) * ((k : M) - 1))‖ ≤ C₁ * ‖(k : M) - 1‖ * R := by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
      let U := Units.oneSub (z t) (hz1 t ht')
      have hUval : (U : M) = 1 + t • ((k : M) - 1) := by simp [U, z, sub_eq_add_neg]
      let g : G := Unitary.toUnits x * U
      have hgval : (g : M) = γ t := by
        change (Unitary.toUnits x : M) * (U : M) = _
        rw [hUval]; rfl
      let Y : M := ((U⁻¹ : Mˣ) : M) * ((k : M) - 1)
      have hgY : (g : M) * Y = (x : M) * ((k : M) - 1) := by
        change (Unitary.toUnits x : M) * (U : M) * (((U⁻¹ : Mˣ) : M) * ((k : M) - 1)) = _
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (U : M), ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mul]
        rfl
      have hUinv : ‖((U⁻¹ : Mˣ) : M)‖ ≤ 2 := by
        have h := tsum_geometric_le_of_norm_lt_one (z t) (hz1 t ht')
        change ‖∑' i : ℕ, z t ^ i‖ ≤ 2
        refine h.trans ?_
        rw [norm_one]
        have := hz t ht'
        have h2 : (1 - ‖z t‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        linarith
      have hY : ‖Y‖ ≤ 2 * ‖(k : M) - 1‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hUinv (norm_nonneg _))
      have hgnorm : ‖(g : M)‖ ≤ 2 * m := by
        rw [hgval]
        refine (norm_mul_le _ _).trans ?_
        have h1 : ‖1 + t • ((k : M) - 1)‖ ≤ 2 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_one]
          have := hz t ht'
          simp only [z, norm_neg] at this
          linarith
        nlinarith [opNorm_unitary_le x, norm_nonneg (1 + t • ((k : M) - 1)),
          norm_nonneg ((x : M))]
      have hginv : ‖((g⁻¹ : G) : M)‖ ≤ 2 * m := by
        have he : ((g⁻¹ : G) : M) = ((U⁻¹ : Mˣ) : M) * ((x⁻¹ : UC) : M) := by
          change (((Unitary.toUnits x * U)⁻¹ : Mˣ) : M) = _
          rw [mul_inv_rev, Units.val_mul, ← map_inv]
          rfl
        rw [he]
        refine (norm_mul_le _ _).trans ?_
        nlinarith [opNorm_unitary_le x⁻¹, norm_nonneg ((U⁻¹ : Mˣ) : M),
          norm_nonneg (((x⁻¹ : UC) : M))]
      have hHg : realMatrixHeight g ≤ H₀ := by
        refine (height_le_opNorms g).trans ?_
        have h1 : ‖(g : M)‖ ^ 2 ≤ (2 * m) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgnorm 2
        have h2 : ‖((g⁻¹ : G) : M)‖ ^ 2 ≤ (2 * m) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hginv 2
        calc
          _ ≤ m ^ 2 * ((2 * m) ^ 2 + (2 * m) ^ 2) := by
            apply mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
          _ = H₀ := by simp only [H₀]; ring
      have hEab (ab : Idx) : ‖rightDerivative I (elem ab) u g‖ ≤ A * R * H₀ ^ N := by
        have hmem := Langlands.Archimedean.rightDerivative_mem_principalSeries _ hu (elem ab)
        have hK : ∀ y ∈ unitaryCompact ℝ (r + 1), ‖rightDerivative I (elem ab) u y‖ ≤ R := by
          intro y hy
          have hy' : Unitary.toUnits (⟨y.val, hy⟩ : UC) = y := Units.ext rfl
          have := hR [ab] (by simp) ⟨y.val, hy⟩
          rw [hy'] at this
          simpa [word, iteratedRightDerivative] using this
        have h0 := hH _ hmem R hK g
        have hHnn : 0 ≤ realMatrixHeight g := RealPlaceRestriction.realMatrixHeight_nonneg g
        refine h0.trans ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHnn hHg N) (mul_nonneg hA hR0)
      have hfd : fderiv ℝ F (γ t) ((x : M) * ((k : M) - 1)) = rightDerivative I Y u g := by
        rw [rightDerivative_eq_fderiv hu.1, hgY, hgval]
      rw [hfd, rightDerivative_eq_sum hu.1]
      calc
        _ ≤ ∑ ab : Idx, ‖(Y ab.1 ab.2 : ℂ) * rightDerivative I (elem ab) u g‖ := norm_sum_le _ _
        _ ≤ ∑ _ab : Idx, (2 * ‖(k : M) - 1‖) * (A * R * H₀ ^ N) := by
          refine Finset.sum_le_sum fun ab _ => ?_
          rw [norm_mul, Complex.norm_real]
          exact mul_le_mul ((norm_entry_le_opNorm Y ab.1 ab.2).trans hY) (hEab ab)
            (norm_nonneg _) (by positivity)
        _ = C₁ * ‖(k : M) - 1‖ * R := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, C₁, m]
          push_cast
          ring
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
      (Set.right_mem_Icc.mpr zero_le_one)
    have hγ1 : F (γ 1) = u (Unitary.toUnits (x * k)) := by
      have : γ 1 = ((Unitary.toUnits (x * k) : G) : M) := by
        simp only [γ, one_smul, add_sub_cancel]
        rfl
      change unitsExtension u (γ 1) = _
      rw [this, unitsExtension_val]
    have hγ0 : F (γ 0) = u (Unitary.toUnits x) := by
      have : γ 0 = ((Unitary.toUnits x : G) : M) := by
        simp only [γ, zero_smul, add_zero, Matrix.mul_one]
        rfl
      change unitsExtension u (γ 0) = _
      rw [this, unitsExtension_val]
    rw [hγ1, hγ0, sub_zero, mul_one] at hmv
    refine hmv.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (norm_nonneg _)) hR0
  · have hk' : 1 / 2 ≤ ‖(k : M) - 1‖ := le_of_not_gt hk
    calc
      _ ≤ ‖u (Unitary.toUnits (x * k))‖ + ‖u (Unitary.toUnits x)‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hval _) (hval _)
      _ ≤ 4 * ‖(k : M) - 1‖ * R := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (norm_nonneg _)) hR0

/-! ## Word bounds of one difference -/

private theorem opNorm_le_entrySum (A : M) : ‖A‖ ≤ entryNorm A := by
  change (‖A‖₊ : ℝ) ≤ _
  rw [Matrix.linfty_opNNNorm_def]
  have h : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ ∑ ab : Idx, ‖A ab.1 ab.2‖₊ := by
    refine Finset.sup_le fun i _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖₊) (fun _ _ => bot_le)
      (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.mpr h
  simpa [entryNorm] using h'

private theorem entryNorm_le_opNorm (A : M) : entryNorm A ≤ (r + 1 : ℝ) ^ 2 * ‖A‖ := by
  unfold entryNorm
  calc
    _ ≤ ∑ _ab : Idx, ‖A‖ := Finset.sum_le_sum fun ab _ => norm_entry_le_opNorm A ab.1 ab.2
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring

private theorem entryNorm_elem (ab : Idx) : entryNorm (elem ab) = 1 := by
  unfold entryNorm elem
  rw [Finset.sum_eq_single ab]
  · simp
  · intro cd _ hcd
    simp only [Matrix.single_apply]
    split_ifs with h
    · exact absurd (Prod.ext h.1 h.2).symm hcd
    · simp
  · simp

theorem iter_mem_principalSeries {ds : List RealBlock} {u : G → ℂ}
    (hu : u ∈ principalSeries ℝ (r + 1) (realPositionCharacter ds)) (Xs : List M) :
    iteratedRightDerivative r Xs u ∈ principalSeries ℝ (r + 1) (realPositionCharacter ds) := by
  induction Xs with
  | nil => exact hu
  | cons X Xs ih =>
    rw [iter_cons]
    exact Langlands.Archimedean.rightDerivative_mem_principalSeries _ ih X

/-- A right difference by a compact element lowers the word order by one and gains a factor of
the displacement of that element. -/
theorem exists_wordBound_difference (ds : List RealBlock) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : G → ℂ), u ∈ principalSeries ℝ (r + 1) (realPositionCharacter ds) →
      ∀ R : ℝ, WordBound (m + 1) u R → ∀ k : UC,
        WordBound m (fun g => u (g * Unitary.toUnits k) - u g) (C * ‖(k : M) - 1‖ * R) := by
  obtain ⟨C₁, hC₁, hone⟩ := exists_oneStep (r := r) ds
  let q : ℝ := (r + 1 : ℝ)
  let δ' : ℝ := q ^ 2 * (q * 2)
  let β : ℝ := max 1 (q ^ 2 * (q * q))
  refine ⟨m * δ' * β ^ m + C₁, by positivity, fun u hu R hR k w hw x => ?_⟩
  have hR0 : 0 ≤ R := hR.nonneg
  have hsm := hu.1
  let kk : G := Unitary.toUnits k
  have hk_inv : ‖((kk⁻¹ : G) : M)‖ ≤ q := by
    have : ((kk⁻¹ : G) : M) = ((k⁻¹ : UC) : M) := by
      change ((Unitary.toUnits k)⁻¹ : G).val = _
      rw [← map_inv]; rfl
    rw [this]; exact opNorm_unitary_le _
  have hk_norm : ‖(kk : M)‖ ≤ q := opNorm_unitary_le k
  -- conjugated letters
  let conj : M → M := fun Y => ((kk⁻¹ : G) : M) * Y * (kk : M)
  have hconj_elem (ab : Idx) :
      entryNorm (conj (elem ab) - elem ab) ≤ δ' * ‖(k : M) - 1‖ ∧
        entryNorm (conj (elem ab)) ≤ β ∧ entryNorm (elem ab) ≤ β := by
    have hE : ‖elem ab‖ ≤ 1 := (opNorm_le_entrySum _).trans (entryNorm_elem ab).le
    have hkinv1 : ((kk⁻¹ : G) : M) * (kk : M) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨?_, ?_, ?_⟩
    · have he : conj (elem ab) - elem ab =
          ((kk⁻¹ : G) : M) * (elem ab * ((kk : M) - 1) - ((kk : M) - 1) * elem ab) := by
        simp only [conj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
          ← Matrix.mul_assoc, hkinv1]
        abel
      rw [he]
      refine (entryNorm_le_opNorm _).trans ?_
      have h1 : ‖((kk⁻¹ : G) : M) * (elem ab * ((kk : M) - 1) - ((kk : M) - 1) * elem ab)‖ ≤
          q * (2 * ‖(k : M) - 1‖) := by
        refine (norm_mul_le _ _).trans (mul_le_mul hk_inv ?_ (norm_nonneg _) (by positivity))
        refine (norm_sub_le _ _).trans ?_
        have a1 : ‖elem ab * ((k : M) - 1)‖ ≤ 1 * ‖(k : M) - 1‖ :=
          (norm_mul_le (elem ab) ((k : M) - 1)).trans
            (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
        have a2 : ‖((k : M) - 1) * elem ab‖ ≤ ‖(k : M) - 1‖ * 1 :=
          (norm_mul_le ((k : M) - 1) (elem ab)).trans
            (mul_le_mul_of_nonneg_left hE (norm_nonneg _))
        change ‖elem ab * ((k : M) - 1)‖ + ‖((k : M) - 1) * elem ab‖ ≤ _
        linarith
      calc
        _ ≤ q ^ 2 * (q * (2 * ‖(k : M) - 1‖)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = δ' * ‖(k : M) - 1‖ := by simp only [δ']; ring
    · refine (entryNorm_le_opNorm _).trans ((mul_le_mul_of_nonneg_left ?_ (by positivity)).trans
        (le_max_right _ _))
      refine (norm_mul_le _ _).trans ?_
      refine mul_le_mul ((norm_mul_le _ _).trans ?_) hk_norm (norm_nonneg _) (by positivity)
      nlinarith [norm_nonneg ((kk⁻¹ : G) : M), norm_nonneg (elem ab)]
    · rw [entryNorm_elem]; exact le_max_left _ _
  have hforall : List.Forall₂ (fun Y Z => entryNorm (Y - Z) ≤ δ' * ‖(k : M) - 1‖ ∧
      entryNorm Y ≤ β ∧ entryNorm Z ≤ β) ((word w).map conj) (word w) := by
    simp only [word, List.map_map]
    induction w with
    | nil => exact List.Forall₂.nil
    | cons ab w ih => exact List.Forall₂.cons (hconj_elem ab) (ih (by simp at hw ⊢; omega))
  -- the iterated derivative of the difference
  have htr : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g => u (g * kk)) := hsm.comp contMDiff_mul_right
  have hsplit : iteratedRightDerivative r (word w) (fun g => u (g * kk) - u g) =
      fun g => iteratedRightDerivative r ((word w).map conj) u (g * kk) -
        iteratedRightDerivative r (word w) u g := by
    have e : (fun g => u (g * kk) - u g) = (fun g => u (g * kk)) - u := rfl
    rw [e, iter_sub htr hsm, iter_translate hsm kk]
    rfl
  rw [hsplit]
  have hxk : Unitary.toUnits x * kk = Unitary.toUnits (x * k) := (map_mul _ _ _).symm
  simp only
  rw [hxk]
  have hlen : ((word w).map conj).length = w.length := by simp [word]
  have hb1 := norm_iter_sub_le hsm (r := r) (le_max_left 1 _) (x * k) [] ((word w).map conj)
    (word w) hforall (R := R) (hR.mono (by simp [word]; omega) le_rfl)
  simp only [List.nil_append, wordNorm, List.map_nil, List.prod_nil, one_mul, hlen] at hb1
  have hv := iter_mem_principalSeries hu (word w)
  have hb2 := hone (iteratedRightDerivative r (word w) u) hv R (fun w' hw' y => by
    have := hR (w' ++ w) (by simp; omega) y
    simpa [word, iter_append] using this) x k
  calc
    _ = ‖(iteratedRightDerivative r ((word w).map conj) u (Unitary.toUnits (x * k)) -
          iteratedRightDerivative r (word w) u (Unitary.toUnits (x * k))) +
        (iteratedRightDerivative r (word w) u (Unitary.toUnits (x * k)) -
          iteratedRightDerivative r (word w) u (Unitary.toUnits x))‖ := by ring_nf
    _ ≤ w.length * (δ' * ‖(k : M) - 1‖) * β ^ w.length * R + C₁ * ‖(k : M) - 1‖ * R :=
      (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ ≤ m * (δ' * ‖(k : M) - 1‖) * β ^ m * R + C₁ * ‖(k : M) - 1‖ * R := by
      have hβ : 1 ≤ β := le_max_left _ _
      have hwm : (w.length : ℝ) ≤ m := by exact_mod_cast hw
      gcongr
    _ = _ := by ring

/-! ## Iterated differences -/

open RealCompactDifferences (rightDifference iteratedDifference displacementProduct
  displacementProduct_nonneg CompactDifferenceBound)

theorem exists_compactDifferenceBound (ds : List RealBlock) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Automorphic.realStandardKFinite (r + 1) ds) (R : ℝ),
      WordBound J (f : G → ℂ) R → CompactDifferenceBound J f (C * R) := by
  choose Cm hCm0 hCm using fun m => exists_wordBound_difference (r := r) ds m
  let D : ℝ := 1 + ∑ m ∈ Finset.range (J + 1), Cm m
  have hD1 : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun m _ => hCm0 m)
  have hCD (m : ℕ) (hm : m ≤ J) : Cm m ≤ D := by
    have := Finset.single_le_sum (f := Cm) (fun m _ => hCm0 m)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    simp only [D]; linarith
  refine ⟨D ^ J, by positivity, fun f R hR => ?_⟩
  have hR0 : 0 ≤ R := hR.nonneg
  have claim : ∀ ks : List UC, ks.length ≤ J →
      WordBound (J - ks.length) ((iteratedDifference ks f : Automorphic.realStandardKFinite (r + 1) ds) :
        Langlands.GeneralLinear (r + 1) ℝ → ℂ) (D ^ ks.length * displacementProduct ks * R) := by
    intro ks
    induction ks with
    | nil => intro _; simpa [iteratedDifference, displacementProduct] using hR
    | cons k ks ih =>
      intro hlen
      simp only [List.length_cons] at hlen
      have hks : ks.length ≤ J := by omega
      set m := J - (ks.length + 1) with hmdef
      have hm1 : J - ks.length = m + 1 := by omega
      let v : Automorphic.realStandardKFinite (r + 1) ds := iteratedDifference ks f
      have hv := ih hks
      rw [hm1] at hv
      have hstep := hCm m v.val v.2.1.1 _ hv k
      have hval : ((iteratedDifference (k :: ks) f : Automorphic.realStandardKFinite (r + 1) ds) :
          Langlands.GeneralLinear (r + 1) ℝ → ℂ) =
          fun g => v.val (g * Unitary.toUnits k) - v.val g := by
        funext g
        have hit : iteratedDifference (k :: ks) f = rightDifference k (iteratedDifference ks f) := by
          simp only [iteratedDifference, List.map_cons, List.prod_cons, Module.End.mul_apply]
        rw [hit]
        change ((Langlands.Archimedean.realStandardRep (r + 1) ds k - 1) v).val g = _
        rw [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub, Pi.sub_apply,
          Langlands.Archimedean.realStandardRep_apply_coe]
        rfl
      rw [hval, List.length_cons]
      refine hstep.mono (by omega) ?_
      have hdp := displacementProduct_nonneg ks
      have hCmD := hCD m (by omega)
      have hkn := norm_nonneg ((k : M) - 1)
      calc
        Cm m * ‖(k : M) - 1‖ * (D ^ ks.length * displacementProduct ks * R) ≤
            D * ‖(k : M) - 1‖ * (D ^ ks.length * displacementProduct ks * R) := by
          gcongr
        _ = D ^ (ks.length + 1) * displacementProduct (k :: ks) * R := by
          simp only [displacementProduct, List.map_cons, List.prod_cons]
          ring
  intro ks hks x
  have h := claim ks hks [] (Nat.zero_le _) x
  simp only [word, List.map_nil] at h
  refine h.trans ?_
  have hdp := displacementProduct_nonneg ks
  calc
    D ^ ks.length * displacementProduct ks * R ≤ D ^ J * displacementProduct ks * R := by
      gcongr
    _ = _ := by ring

/-- A uniform bound for all elementary right-derivative words of order at most `J` on the
compact group gives a compact difference bound of order `J`. -/
def RealCompactDerivativeDifferencesStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (J : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : Automorphic.realStandardKFinite (r + 1) ds) (R : ℝ),
      WordBound J (f : Langlands.GeneralLinear (r + 1) ℝ → ℂ) R →
        CompactDifferenceBound J f (C * R)

theorem realCompactDerivativeDifferences : RealCompactDerivativeDifferencesStatement :=
  fun r ds J => exists_compactDifferenceBound (r := r) ds J

end Langlands.Global.RankinSelbergGlobal.RealCompactDerivativeDifferences
