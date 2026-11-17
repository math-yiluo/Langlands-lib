import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Minors of matrices as the matrices of exterior powers

For `k`-element subsets `S, T` of `Fin n`, `minorMat A S T` is the minor of `A` with rows `S` and
columns `T`, defined as the matrix coefficient of `Λ^k A` in the basis `e_S`. Multiplicativity
(Cauchy–Binet) is functoriality of `Λ^k`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff Manifold

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.JacquetTranslation

open Langlands.GeneralLinear

variable {n k : ℕ}

/-- The `k`-element subsets of `Fin n`. -/
abbrev Sub (n k : ℕ) := Set.powersetCard (Fin n) k

/-- The increasing enumeration of a `k`-element subset. -/
abbrev enum (S : Sub n k) : Fin k ↪o Fin n := Set.powersetCard.ofFinEmbEquiv.symm S

/-- The basis `e_S` of `Λ^k ℂ^n`. -/
abbrev extBasis (n k : ℕ) : Module.Basis (Sub n k) ℂ (⋀[ℂ]^k (Fin n → ℂ)) :=
  (Pi.basisFun ℂ (Fin n)).exteriorPower k

/-- The minors of `A`: the matrix of `Λ^k A` in the basis `e_S`. -/
def minorMat (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ :=
  LinearMap.toMatrix (extBasis n k) (extBasis n k) (exteriorPower.map k (Matrix.toLin' A))

theorem minorMat_mul (A B : Matrix (Fin n) (Fin n) ℂ) :
    (minorMat (A * B) : Matrix (Sub n k) (Sub n k) ℂ) = minorMat A * minorMat B := by
  simp only [minorMat, Matrix.toLin'_mul, exteriorPower.map_comp]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem minorMat_one : (minorMat (1 : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) =
    1 := by
  simp only [minorMat, Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

/-- The minor as a determinant. -/
theorem minorMat_apply (A : Matrix (Fin n) (Fin n) ℂ) (S T : Sub n k) :
    minorMat A S T = (Matrix.of fun i j : Fin k => A (enum S i) (enum T j)).det := by
  rw [minorMat, LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti,
    ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.toLin'_apply]

theorem minorMat_transpose (A : Matrix (Fin n) (Fin n) ℂ) (S T : Sub n k) :
    minorMat Aᵀ S T = minorMat A T S := by
  rw [minorMat_apply, minorMat_apply, ← Matrix.det_transpose]
  congr 1

theorem minorMat_map_conj (A : Matrix (Fin n) (Fin n) ℂ) (S T : Sub n k) :
    minorMat (A.map (starRingEnd ℂ)) S T = starRingEnd ℂ (minorMat A S T) := by
  rw [minorMat_apply, minorMat_apply, RingHom.map_det]
  congr 1

/-- The sum of the elements of `S` through its enumeration. -/
theorem sum_enum (S : Sub n k) (f : Fin n → ℕ) :
    ∑ i : Fin k, f (enum S i) = ∑ s ∈ (S : Finset (Fin n)), f s := by
  have h := Finset.map_orderEmbOfFin_univ (S : Finset (Fin n)) S.prop
  rw [← h, Finset.sum_map]
  rfl

theorem prod_enum (S : Sub n k) (f : Fin n → ℂ) :
    ∏ i : Fin k, f (enum S i) = ∏ s ∈ (S : Finset (Fin n)), f s := by
  have h := Finset.map_orderEmbOfFin_univ (S : Finset (Fin n)) S.prop
  rw [← h, Finset.prod_map]
  rfl

theorem mem_iff_exists_enum (S : Sub n k) (x : Fin n) : x ∈ (S : Finset (Fin n)) ↔
    ∃ i, enum S i = x := by
  exact Set.powersetCard.mem_coe_iff.trans
    ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S x).symm.trans Set.mem_range)

/-- The weight `ΣS` of a subset. -/
def wt (S : Sub n k) : ℕ := ∑ s ∈ (S : Finset (Fin n)), (s : ℕ)

/-- For upper triangular `b`, a nonzero minor `(S, T)` has `wt S ≤ wt T`, with equality only
if `S = T`. -/
theorem minorMat_upper_ne_zero {b : Matrix (Fin n) (Fin n) ℂ} (hb : ∀ i j, j < i → b i j = 0)
    {S T : Sub n k} (h : minorMat b S T ≠ 0) : wt S ≤ wt T ∧ (wt S = wt T → S = T) := by
  classical
  rw [minorMat_apply, Matrix.det_apply] at h
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hprod : ∏ i, b (enum S (σ i)) (enum T i) ≠ 0 := by
    intro h0
    apply hσ
    simp only [Matrix.of_apply] at h0 ⊢
    rw [h0, smul_zero]
  rw [Finset.prod_ne_zero_iff] at hprod
  have hle : ∀ i, enum S (σ i) ≤ enum T i := by
    intro i
    by_contra hlt
    exact hprod i (Finset.mem_univ _) (hb _ _ (lt_of_not_ge hlt))
  have hle' : ∀ i ∈ (Finset.univ : Finset (Fin k)), ((enum S (σ i) : Fin n) : ℕ) ≤ (enum T i : ℕ) :=
    fun i _ => hle i
  have hsumσ : ∑ i, ((enum S (σ i) : Fin n) : ℕ) = wt S := by
    rw [wt, ← sum_enum S (fun s => (s : ℕ))]
    exact Equiv.sum_comp σ (fun i => ((enum S i : Fin n) : ℕ))
  have hsumT : ∑ i, ((enum T i : Fin n) : ℕ) = wt T := by
    rw [wt, ← sum_enum T (fun s => (s : ℕ))]
  refine ⟨?_, fun heq => ?_⟩
  · rw [← hsumσ, ← hsumT]
    exact Finset.sum_le_sum hle'
  · rw [← hsumσ, ← hsumT] at heq
    have hall := (Finset.sum_eq_sum_iff_of_le hle').mp heq
    have hval : ∀ i, enum S (σ i) = enum T i := fun i =>
      Fin.ext (hall i (Finset.mem_univ _))
    apply Subtype.ext
    ext x
    rw [mem_iff_exists_enum, mem_iff_exists_enum]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨σ.symm i, by rw [← hval, Equiv.apply_symm_apply]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨σ i, hval i⟩

/-- The diagonal minors of an upper triangular matrix. -/
theorem minorMat_upper_self {b : Matrix (Fin n) (Fin n) ℂ} (hb : ∀ i j, j < i → b i j = 0)
    (S : Sub n k) : minorMat b S S = ∏ s ∈ (S : Finset (Fin n)), b s s := by
  rw [minorMat_apply, Matrix.det_of_isUpperTriangular, ← prod_enum]
  · rfl
  · intro i j hij
    exact hb _ _ ((enum S).lt_iff_lt.mpr hij)

/-- The minors of a diagonal matrix. -/
theorem minorMat_diagonal (v : Fin n → ℂ) (S T : Sub n k) :
    minorMat (Matrix.diagonal v) S T = if S = T then ∏ s ∈ (S : Finset (Fin n)), v s else 0 := by
  have hb : ∀ i j : Fin n, j < i → Matrix.diagonal v i j = 0 := fun i j h =>
    Matrix.diagonal_apply_ne _ (ne_of_gt h)
  split_ifs with hST
  · subst hST
    rw [minorMat_upper_self hb]
    simp
  · by_contra h
    have h1 := minorMat_upper_ne_zero hb h
    have h' : minorMat (Matrix.diagonal v) T S ≠ 0 := by
      rwa [← minorMat_transpose, Matrix.diagonal_transpose]
    have h2 := minorMat_upper_ne_zero hb h'
    exact hST (h1.2 (le_antisymm h1.1 h2.1))

/-! ## The last `k` positions -/

/-- The last `k` positions `{n - k, …, n - 1}` (for `k ≤ n`). -/
def lowSub (n k : ℕ) (hk : k ≤ n) : Sub n k :=
  ⟨Finset.univ.filter (fun j : Fin n => n ≤ (j : ℕ) + k), by
    show (Finset.univ.filter (fun j : Fin n => n ≤ (j : ℕ) + k)).card = k
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j : Fin n => n ≤ (j : ℕ) + k)
    have h2 : (Finset.univ.filter (fun j : Fin n => ¬ n ≤ (j : ℕ) + k)) =
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < n - k) :=
      Finset.filter_congr (fun j _ => by omega)
    rw [h2, Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at h1
    omega⟩

theorem mem_lowSub {hk : k ≤ n} (j : Fin n) :
    j ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)) ↔ n ≤ (j : ℕ) + k := by
  simp [lowSub]

/-- The row `lowSub` of the minors of an upper triangular matrix. -/
theorem minorMat_upper_low {b : Matrix (Fin n) (Fin n) ℂ} (hb : ∀ i j, j < i → b i j = 0)
    (hk : k ≤ n) (U : Sub n k) :
    minorMat b (lowSub n k hk) U =
      if U = lowSub n k hk then ∏ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), b r r
      else 0 := by
  split_ifs with hU
  · rw [hU, minorMat_upper_self hb]
  · -- some element of `U` lies below `n - k`
    obtain ⟨u, hu, hulow⟩ : ∃ u ∈ (U : Finset (Fin n)), ¬ n ≤ (u : ℕ) + k := by
      by_contra h
      push Not at h
      apply hU
      apply Subtype.ext
      refine (Finset.eq_of_subset_of_card_le (fun u hu => (mem_lowSub u).mpr (h u hu)) ?_)
      rw [U.prop, (lowSub n k hk).prop]
    obtain ⟨j, rfl⟩ := (mem_iff_exists_enum U u).mp hu
    rw [minorMat_apply]
    refine Matrix.det_eq_zero_of_column_eq_zero j (fun i => ?_)
    simp only [Matrix.of_apply]
    apply hb
    have hi : n ≤ ((enum (lowSub n k hk) i : Fin n) : ℕ) + k :=
      (mem_lowSub _).mp ((mem_iff_exists_enum _ _).mpr ⟨i, rfl⟩)
    show ((enum U j : Fin n) : ℕ) < ((enum (lowSub n k hk) i : Fin n) : ℕ)
    omega

/-! ## Holomorphic and antiholomorphic minors -/

/-- `y` itself (`anti = false`) or its entrywise complex conjugate (`anti = true`). -/
def phi (anti : Bool) (y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  if anti then y.map (starRingEnd ℂ) else y

theorem phi_mul (anti : Bool) (y z : Matrix (Fin n) (Fin n) ℂ) :
    phi anti (y * z) = phi anti y * phi anti z := by
  cases anti <;> simp [phi, Matrix.map_mul]

theorem phi_one (anti : Bool) : phi anti (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  cases anti <;> simp [phi, Matrix.map_one]

/-- The holomorphic (`anti = false`) or antiholomorphic (`anti = true`) minors. -/
def mm (anti : Bool) (y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ :=
  minorMat (phi anti y)

theorem mm_mul (anti : Bool) (y z : Matrix (Fin n) (Fin n) ℂ) :
    (mm anti (y * z) : Matrix (Sub n k) (Sub n k) ℂ) = mm anti y * mm anti z := by
  rw [mm, phi_mul, minorMat_mul]
  rfl

theorem mm_one (anti : Bool) : (mm anti (1 : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Sub n k) (Sub n k) ℂ) = 1 := by
  rw [mm, phi_one, minorMat_one]

theorem contDiff_phi_entry (anti : Bool) (a b : Fin n) :
    ContDiff ℝ ⊤ (fun y : Matrix (Fin n) (Fin n) ℂ => phi anti y a b) := by
  let e : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun y => y a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : ContDiff ℝ ⊤ (fun y : Matrix (Fin n) (Fin n) ℂ => y a b) :=
    (LinearMap.toContinuousLinearMap e).contDiff
  cases anti
  · simpa [phi] using he
  · have h2 := Complex.conjCLE.contDiff.comp he
    simp only [phi, ite_true, Matrix.map_apply]
    exact h2

theorem contDiff_mm (anti : Bool) (S T : Sub n k) :
    ContDiff ℝ ⊤ (fun y : Matrix (Fin n) (Fin n) ℂ => (mm anti y : Matrix (Sub n k) (Sub n k) ℂ) S T) := by
  simp only [mm, minorMat_apply, Matrix.det_apply, Matrix.of_apply]
  refine ContDiff.sum (fun σ _ => ?_)
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod (fun i _ => contDiff_phi_entry anti _ _))

theorem contMDiff_mm (anti : Bool) (S T : Sub n k) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (fun g : Langlands.GeneralLinear n ℂ =>
      (mm anti (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S T) :=
  contMDiff_of_contDiffOn (((contDiff_mm anti S T).of_le le_top).contDiffOn) (fun _ => rfl)

/-! ## Right derivatives of minors -/

/-- The derivative at the identity of the minor `(U, T)` in the direction `X`: the matrix
coefficient of the derived action of `X` on `Λ^k`. -/
def Dco (anti : Bool) (U T : Sub n k) (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  fderiv ℝ (fun y : Matrix (Fin n) (Fin n) ℂ => (mm anti y : Matrix (Sub n k) (Sub n k) ℂ) U T) 1 X

theorem differentiableAt_mm (anti : Bool) (S T : Sub n k) (y : Matrix (Fin n) (Fin n) ℂ) :
    DifferentiableAt ℝ (fun y : Matrix (Fin n) (Fin n) ℂ =>
      (mm anti y : Matrix (Sub n k) (Sub n k) ℂ) S T) y :=
  (contDiff_mm anti S T).differentiable (by simp) y

/-- The right derivative of a minor function, by Cauchy–Binet. -/
theorem rightDerivative_mm (anti : Bool) (S T : Sub n k) (X : Matrix (Fin n) (Fin n) ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (fun g : Langlands.GeneralLinear n ℂ =>
        (mm anti (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S T) g =
      ∑ U, (mm anti (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S U *
        Dco anti U T X := by
  set c : Sub n k → ℂ := fun U =>
    (mm anti (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S U with hc
  have hψ : (fun y : Matrix (Fin n) (Fin n) ℂ =>
      (mm anti ((g : Matrix (Fin n) (Fin n) ℂ) * y) : Matrix (Sub n k) (Sub n k) ℂ) S T) =
      fun y => ∑ U, c U * (mm anti y : Matrix (Sub n k) (Sub n k) ℂ) U T := by
    funext y
    rw [mm_mul, Matrix.mul_apply]
  have hfd : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ =>
      ∑ U, c U * (mm anti y : Matrix (Sub n k) (Sub n k) ℂ) U T)
      (∑ U, c U • fderiv ℝ (fun y : Matrix (Fin n) (Fin n) ℂ =>
        (mm anti y : Matrix (Sub n k) (Sub n k) ℂ) U T) 1) 1 :=
    HasFDerivAt.fun_sum (fun U _ => ((differentiableAt_mm anti U T 1).hasFDerivAt.const_mul (c U)))
  have hdψ : DifferentiableAt ℝ (fun y : Matrix (Fin n) (Fin n) ℂ =>
      (mm anti ((g : Matrix (Fin n) (Fin n) ℂ) * y) : Matrix (Sub n k) (Sub n k) ℂ) S T)
      ((1 : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hψ, Units.val_one]
    exact hfd.differentiableAt
  unfold rightDerivative
  rw [mfderiv_eq_fderiv_of_eq_comp (ψ := fun y : Matrix (Fin n) (Fin n) ℂ =>
      (mm anti ((g : Matrix (Fin n) (Fin n) ℂ) * y) : Matrix (Sub n k) (Sub n k) ℂ) S T)
      (fun h => congrArg (fun y : Matrix (Fin n) (Fin n) ℂ =>
        (mm anti y : Matrix (Sub n k) (Sub n k) ℂ) S T) (Units.val_mul g h)) 1 hdψ,
      Units.val_one, hψ, hfd.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, Dco, hc]
  rfl

/-- `Dco` as the derivative along the line `t ↦ 1 + t X`. -/
theorem hasDerivAt_mm_line (anti : Bool) (U T : Sub n k) (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (mm anti (1 + t • X) : Matrix (Sub n k) (Sub n k) ℂ) U T)
      (Dco anti U T X) 0 := by
  have hf : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ =>
      (mm anti y : Matrix (Sub n k) (Sub n k) ℂ) U T)
      (fderiv ℝ (fun y : Matrix (Fin n) (Fin n) ℂ =>
        (mm anti y : Matrix (Sub n k) (Sub n k) ℂ) U T) 1) (1 + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (differentiableAt_mm anti U T 1).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • X) X 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Matrix (Fin n) (Fin n) ℂ)
    simpa only [id, one_smul] using this
  exact hf.comp_hasDerivAt (0 : ℝ) hl

/-- The minors in the row `lowSub` along the line `1 + t X`, `X` upper triangular. -/
theorem mm_line_low (anti : Bool) (hk : k ≤ n) (U : Sub n k) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, j < i → X i j = 0) (t : ℝ) :
    (mm anti (1 + t • X) : Matrix (Sub n k) (Sub n k) ℂ) (lowSub n k hk) U =
      if U = lowSub n k hk then
        ∏ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), (1 + (t : ℂ) * phi anti X r r)
      else 0 := by
  have hentry : ∀ i j, phi anti (1 + t • X) i j =
      (if i = j then 1 else 0) + (t : ℂ) * phi anti X i j := by
    intro i j
    cases anti <;> by_cases hij : i = j <;>
      simp [phi, hij, Complex.real_smul, map_add, map_mul]
  have hb : ∀ i j, j < i → phi anti (1 + t • X) i j = 0 := by
    intro i j hji
    rw [hentry, if_neg (ne_of_gt hji)]
    have : phi anti X i j = 0 := by
      cases anti <;> simp [phi, hX i j hji]
    rw [this]; ring
  rw [mm, minorMat_upper_low hb hk U]
  split_ifs
  · refine Finset.prod_congr rfl (fun r _ => ?_)
    rw [hentry, if_pos rfl]
  · rfl

/-- The derived action on the row `lowSub`, for upper triangular directions. -/
theorem Dco_low (anti : Bool) (hk : k ≤ n) (U : Sub n k) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, j < i → X i j = 0) :
    Dco anti (lowSub n k hk) U X =
      if U = lowSub n k hk then ∑ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), phi anti X r r
      else 0 := by
  have h1 := hasDerivAt_mm_line anti (lowSub n k hk) U X
  by_cases hU : U = lowSub n k hk
  · subst hU
    have hfun : (fun t : ℝ => (mm anti (1 + t • X) : Matrix (Sub n k) (Sub n k) ℂ)
        (lowSub n k hk) (lowSub n k hk)) = fun t : ℝ =>
          ∏ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), (1 + (t : ℂ) * phi anti X r r) :=
      funext fun t => by rw [mm_line_low anti hk _ hX t, if_pos rfl]
    rw [hfun] at h1
    rw [if_pos rfl]
    have h2 : HasDerivAt (fun t : ℝ =>
        ∏ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), (1 + (t : ℂ) * phi anti X r r))
        (∑ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), phi anti X r r) 0 := by
      have := HasDerivAt.fun_finsetProd (u := ((lowSub n k hk : Sub n k) : Finset (Fin n)))
        (f := fun r (t : ℝ) => (1 : ℂ) + (t : ℂ) * phi anti X r r)
        (f' := fun r => phi anti X r r) (x := (0 : ℝ)) (fun r _ => by
          simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const
            (phi anti X r r)).const_add (1 : ℂ))
      simpa using this
    exact h1.unique h2
  · have hfun : (fun t : ℝ => (mm anti (1 + t • X) : Matrix (Sub n k) (Sub n k) ℂ)
        (lowSub n k hk) U) = fun _ : ℝ => (0 : ℂ) :=
      funext fun t => by rw [mm_line_low anti hk _ hX t, if_neg hU]
    rw [hfun] at h1
    rw [if_neg hU]
    exact h1.unique (hasDerivAt_const _ _)

end Langlands.Archimedean.JacquetTranslation
