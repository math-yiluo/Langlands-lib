import Langlands.Global.RankinSelberg.UnfoldingCoefficient
import Langlands.Global.RankinSelberg.UnfoldingWhittaker
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # General linear facts for the unfolding of unequal-rank integrals -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global PrimitiveAdelicHeight

local instance unfoldingGLSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unfoldingGLSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section PadMatrix

variable {R : Type*} [CommRing R]

/-- The entries of `diag(g, I)`. -/
theorem padGL_apply {m n : ℕ} (h : m ≤ n) (g : Matrix.GeneralLinearGroup (Fin m) R)
    (i j : Fin n) :
    ((padGL h g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      if hi : (i : ℕ) < m then
        (if hj : (j : ℕ) < m then (g : Matrix (Fin m) (Fin m) R) ⟨i, hi⟩ ⟨j, hj⟩ else 0)
      else (if i = j then 1 else 0) := by
  have key : ∀ (k : ℕ) (A : Matrix (Fin m) (Fin m) R) (a b : Fin (m + k)),
      padMatrix m k A a b =
        if hi : (a : ℕ) < m then
          (if hj : (b : ℕ) < m then A ⟨a, hi⟩ ⟨b, hj⟩ else 0)
        else (if a = b then 1 else 0) := by
    intro k A a b
    simp only [padMatrix, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    refine Fin.addCases (fun a₀ => ?_) (fun a₁ => ?_) a <;>
      refine Fin.addCases (fun b₀ => ?_) (fun b₁ => ?_) b <;>
      (simp [Fin.ext_iff, Matrix.one_apply]; try omega)
  change Matrix.reindex _ _ (padMatrix m (n - m) (g : Matrix (Fin m) (Fin m) R)) i j = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, key]
  simp [Fin.ext_iff]

end PadMatrix

variable (F : Type u) [Field F] [NumberField F]

section Pad

/-- Padding is multiplicative on adelic points. -/
theorem pad_mul {m n : ℕ} (h : m ≤ n) (x y : Points F m) :
    pad F h (x * y) = pad F h x * pad F h y := by
  simp only [pad, map_mul]

/-- The matrix of a padded adelic point. -/
theorem adelicEquiv_pad {m n : ℕ} (h : m ≤ n) (x : Points F m) :
    GeneralLinearGroupPoints.adelicEquiv F n (pad F h x) =
      padGL h (GeneralLinearGroupPoints.adelicEquiv F m x) := by
  simp only [pad, MulEquiv.apply_symm_apply]

/-- Padding is continuous. -/
theorem continuous_pad {m n : ℕ} (h : m ≤ n) : Continuous (pad F h) := by
  have hpm : Continuous (fun A : Matrix (Fin m) (Fin m) (Adeles F) =>
      padMatrix (R := Adeles F) m (n - m) A) := by
    change Continuous fun A : Matrix (Fin m) (Fin m) (Adeles F) =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin (n - m)) (Fin (n - m)) (Adeles F)))
    exact (continuous_id.matrix_fromBlocks continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  have hp : Continuous (padGL (R := Adeles F) h) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · change Continuous fun g : Matrix.GeneralLinearGroup (Fin m) (Adeles F) =>
        Matrix.reindex (finCongr (Nat.add_sub_of_le h)) (finCongr (Nat.add_sub_of_le h))
          (padMatrix (R := Adeles F) m (n - m) (g : Matrix (Fin m) (Fin m) (Adeles F)))
      exact (hpm.comp Units.continuous_val).matrix_reindex _ _
    · change Continuous fun g : Matrix.GeneralLinearGroup (Fin m) (Adeles F) =>
        Matrix.reindex (finCongr (Nat.add_sub_of_le h)) (finCongr (Nat.add_sub_of_le h))
          (padMatrix (R := Adeles F) m (n - m) (↑g⁻¹ : Matrix (Fin m) (Fin m) (Adeles F)))
      exact (hpm.comp Units.continuous_coe_inv).matrix_reindex _ _
  exact (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
    (hp.comp (GeneralLinearGroupPoints.adelicHomeomorph F m).continuous)

/-- Padding preserves upper unitriangularity. -/
theorem isUnitriangular_padGL {R : Type*} [CommRing R] {m n : ℕ} (h : m ≤ n)
    (g : Matrix.GeneralLinearGroup (Fin m) R)
    (hg : IsUnitriangular (g : Matrix (Fin m) (Fin m) R)) :
    IsUnitriangular ((padGL h g : Matrix.GeneralLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : (j : ℕ) < i := hij
    rw [padGL_apply]
    split_ifs with hi hj hij2
    · exact hg.1 (show (⟨j, hj⟩ : Fin m) < ⟨i, hi⟩ from hij')
    · rfl
    · exact absurd (congrArg Fin.val hij2) (by omega)
    · rfl
  · rw [padGL_apply]
    by_cases hi : (i : ℕ) < m
    · simp only [dite_eq_left hi]
      exact hg.2 _
    · simp [dite_eq_right hi]

/-- Padding maps `N_m(𝔸)` into `N_n(𝔸)`. -/
theorem pad_mem_unipotentAdelic {m n : ℕ} (h : m ≤ n) (x : unipotentAdelic F m) :
    pad F h (x : Points F m) ∈ unipotentAdelic F n := by
  rw [mem_unipotentAdelic_iff, adelicEquiv_pad]
  exact isUnitriangular_padGL h _ (isUnitriangular_of_mem_unipotentAdelic F x)

/-- Padding as a map `N_m(𝔸) → N_n(𝔸)`. -/
def padUnipotent {m n : ℕ} (h : m ≤ n) (x : unipotentAdelic F m) : unipotentAdelic F n :=
  ⟨pad F h (x : Points F m), pad_mem_unipotentAdelic F h x⟩

/-- The superdiagonal sum of `diag(g, I)` is that of `g`. -/
theorem sum_superdiag_padGL {R : Type*} [CommRing R] {t r : ℕ} (h : t + 1 ≤ r + 1)
    (g : Matrix.GeneralLinearGroup (Fin (t + 1)) R) :
    ∑ i : Fin r, ((padGL h g : Matrix.GeneralLinearGroup (Fin (r + 1)) R) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) R) i.castSucc i.succ =
      ∑ i : Fin t, (g : Matrix (Fin (t + 1)) (Fin (t + 1)) R) i.castSucc i.succ := by
  set A : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
    ((padGL h g : Matrix.GeneralLinearGroup (Fin (r + 1)) R) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) R) with hA
  set B : Matrix (Fin (t + 1)) (Fin (t + 1)) R :=
    (g : Matrix (Fin (t + 1)) (Fin (t + 1)) R) with hB
  have htr : t ≤ r := by omega
  let fA : ℕ → R := fun k => if hk : k + 1 < r + 1 then A ⟨k, by omega⟩ ⟨k + 1, hk⟩ else 0
  let fB : ℕ → R := fun k => if hk : k + 1 < t + 1 then B ⟨k, by omega⟩ ⟨k + 1, hk⟩ else 0
  have h1 : ∑ i : Fin r, A i.castSucc i.succ = ∑ k ∈ Finset.range r, fA k := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [fA, dite_eq_left (show (i : ℕ) + 1 < r + 1 by omega)]
    rfl
  have h2 : ∑ i : Fin t, B i.castSucc i.succ = ∑ k ∈ Finset.range t, fB k := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [fB, dite_eq_left (show (i : ℕ) + 1 < t + 1 by omega)]
    rfl
  rw [h1, h2, ← Finset.sum_range_add_sum_Ico _ htr]
  have h3 : ∑ k ∈ Finset.Ico t r, fA k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' := Finset.mem_Ico.mp hk
    simp only [fA, dite_eq_left (show k + 1 < r + 1 by omega), A]
    rw [padGL_apply]
    simp only [dite_eq_right (show ¬ (k + 1 < t + 1) by omega)]
    split_ifs with hi he
    · rfl
    · exact absurd (congrArg Fin.val he) (by simp)
    · rfl
  rw [h3, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  simp only [fA, fB, dite_eq_left (show k + 1 < r + 1 by omega),
    dite_eq_left (show k + 1 < t + 1 by omega),
    A, B]
  rw [padGL_apply]
  simp only [dite_eq_left (show k < t + 1 by omega), dite_eq_left (show k + 1 < t + 1 by omega)]

/-- The generic character of `diag(n, I)` is that of `n`. -/
theorem genericCharacter_padUnipotent {t r : ℕ} (h : t + 1 ≤ r + 1) (ψ : AddChar (Adeles F) ℂ)
    (x : unipotentAdelic F (t + 1)) :
    genericCharacter F r ψ (fun _ => 1) (padUnipotent F h x) =
      genericCharacter F t ψ (fun _ => 1) x := by
  simp only [genericCharacter, map_one, one_mul]
  change ψ (∑ i : Fin r, ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)
      (pad F h (x : Points F (t + 1))) : Matrix.GeneralLinearGroup _ _) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i.castSucc i.succ) = _
  rw [adelicEquiv_pad, sum_superdiag_padGL]

end Pad

section Determinant

/-- The determinant norm is multiplicative. -/
theorem detNorm_mul (n : ℕ) (x y : Points F n) :
    detNorm F n (x * y) = detNorm F n x * detNorm F n y := by
  simp only [detNorm, map_mul, Units.val_mul, NNReal.coe_mul]

/-- The determinant norm is positive. -/
theorem detNorm_pos (n : ℕ) (x : Points F n) : 0 < detNorm F n x := by
  unfold detNorm
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))

/-- The determinant norm is continuous. -/
theorem continuous_detNorm (n : ℕ) : Continuous (detNorm F n) := by
  unfold detNorm
  exact NNReal.continuous_coe.comp (Units.continuous_val.comp
    ((AdelicBlockDeterminantCharacter.determinantNorm F n).continuous.comp
      (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous))

/-- The determinant norm of a rational point is one. -/
theorem detNorm_rational (n : ℕ) (q : RationalGroupPoints F (Scheme F n)) :
    detNorm F n (AdelicGroupPoints.rational F (Scheme F n) q) = 1 := by
  simp only [detNorm, GeneralLinearGroupPoints.adelicEquiv_rational,
    AdelicBlockDeterminantCharacter.determinantNorm_rational, Units.val_one, NNReal.coe_one]

/-- The determinant norm is trivial on the rational subgroup. -/
theorem detNorm_of_mem_rationalSubgroup (n : ℕ) {x : Points F n}
    (hx : x ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) : detNorm F n x = 1 := by
  obtain ⟨q, rfl⟩ := hx
  exact detNorm_rational F n q

/-- The determinant norm is trivial on `N_n(𝔸)`. -/
theorem detNorm_unipotent (n : ℕ) (x : unipotentAdelic F n) : detNorm F n x = 1 := by
  have hdet : Matrix.GeneralLinearGroup.det
      (GeneralLinearGroupPoints.adelicEquiv F n (x : Points F n)) = 1 := by
    ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact (isUnitriangular_of_mem_unipotentAdelic F x).det_eq_one
  simp only [detNorm, AdelicBlockDeterminantCharacter.determinantNorm]
  change (((IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det
    (GeneralLinearGroupPoints.adelicEquiv F n (x : Points F n))) : NNReal)) : ℝ) = 1
  rw [hdet, map_one, Units.val_one, NNReal.coe_one]

/-- The determinant power is multiplicative. -/
theorem detPower_mul (n : ℕ) (x y : Points F n) (s : ℂ) :
    detPower F n (x * y) s = detPower F n x s * detPower F n y s := by
  simp only [detPower, detNorm_mul, ← Complex.exp_add]
  rw [Real.log_mul (detNorm_pos F n x).ne' (detNorm_pos F n y).ne']
  push_cast
  ring_nf

/-- The determinant power is exponential in the exponent. -/
theorem detPower_add (n : ℕ) (x : Points F n) (s s' : ℂ) :
    detPower F n x (s + s') = detPower F n x s * detPower F n x s' := by
  simp only [detPower, ← Complex.exp_add, add_mul]

/-- The determinant power at a point of norm one is one. -/
theorem detPower_of_detNorm_eq_one (n : ℕ) {x : Points F n} (hx : detNorm F n x = 1) (s : ℂ) :
    detPower F n x s = 1 := by
  simp [detPower, hx]

/-- The determinant power is continuous. -/
theorem continuous_detPower (n : ℕ) (s : ℂ) : Continuous fun x => detPower F n x s := by
  unfold detPower
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact Complex.continuous_ofReal.comp
    ((continuous_detNorm F n).log fun x => (detNorm_pos F n x).ne')

/-- Left translation by rational points does not change the determinant power. -/
theorem detPower_rational_mul (n : ℕ) {k : Points F n}
    (hk : k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) (x : Points F n) (s : ℂ) :
    detPower F n (k * x) s = detPower F n x s := by
  rw [detPower_mul, detPower_of_detNorm_eq_one F n (detNorm_of_mem_rationalSubgroup F n hk),
    one_mul]

/-- Left translation by `N_n(𝔸)` does not change the determinant power. -/
theorem detPower_unipotent_mul (n : ℕ) (u : unipotentAdelic F n) (x : Points F n) (s : ℂ) :
    detPower F n ((u : Points F n) * x) s = detPower F n x s := by
  rw [detPower_mul, detPower_of_detNorm_eq_one F n (detNorm_unipotent F n u), one_mul]

end Determinant

section Whittaker

/-- Elements of the rational unipotent subgroup are rational points. -/
theorem mem_rationalSubgroup_of_unipotent {n : ℕ}
    (k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n)) :
    ((k : unipotentAdelic F n) : Points F n) ∈
      AdelicGroupPoints.rationalSubgroup F (Scheme F n) := by
  obtain ⟨q, hq⟩ := k.property
  rw [← hq]
  exact ⟨q.val, rfl⟩

variable [CompactSpace (AdeleQuotient F)]

/-- Cusp functions are continuous. -/
theorem continuous_cuspFunction {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (v : T.Space) : Continuous (cuspFunction F T v) :=
  continuous_evaluate F (Scheme F (r + 1)) _

/-- Cusp functions are left invariant under rational points. -/
theorem cuspFunction_rational_mul {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (v : T.Space) {k : Points F (r + 1)}
    (hk : k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1))) (x : Points F (r + 1)) :
    cuspFunction F T v (k * x) = cuspFunction F T v x :=
  evaluate_rational_mul F (Scheme F (r + 1)) _ ⟨k, hk⟩ x

/-- Equivariance of the cusp Whittaker function under `N_(r+1)(𝔸)`. -/
theorem cuspWhittaker_mul_left {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (u : unipotentAdelic F (r + 1)) (g : Points F (r + 1)) :
    cuspWhittaker F T ψ v ((u : Points F (r + 1)) * g) =
      genericCharacter F r ψ (fun _ => 1) u * cuspWhittaker F T ψ v g := by
  have := compactSpace_unipotentRationalQuotient F (r + 1)
  exact subgroupCharacterCoefficient_mul_left F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
    (genericCharacter F r ψ fun _ => 1) (genericCharacter_mul F r ψ _)
    (genericCharacter_rational F r ψ hψ.2.2.1 _) (norm_genericCharacter F r ψ hψ.2.2.2 _)
    (cuspFunction F T v)
    (fun k x => cuspFunction_rational_mul F T v (mem_rationalSubgroup_of_unipotent F k) x) u g

omit [CompactSpace (AdeleQuotient F)] in
/-- The generic character is left invariant under rational unipotent points. -/
theorem genericCharacter_rational_mul (r : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ)
    (k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
    (n : unipotentAdelic F (r + 1)) :
    genericCharacter F r ψ (fun _ => 1) (k * n) = genericCharacter F r ψ (fun _ => 1) n := by
  rw [genericCharacter_mul, genericCharacter_rational F r ψ hψ.2.2.1, one_mul]

/-- Cusp Whittaker functions are measurable. -/
theorem measurable_cuspWhittaker {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) :
    Measurable (cuspWhittaker F T ψ v) :=
  measurable_subgroupCharacterCoefficient F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
    (genericCharacter F r ψ fun _ => 1) (continuous_genericCharacter F r ψ hψ.1 _).measurable
    (genericCharacter_rational_mul F r ψ hψ) (cuspFunction F T v)
    (continuous_cuspFunction F T v).measurable
    (fun k x => cuspFunction_rational_mul F T v (mem_rationalSubgroup_of_unipotent F k) x)

omit [CompactSpace (AdeleQuotient F)] in
/-- The inverse of a standard additive character is standard. -/
theorem isStandardAdditiveCharacter_inv (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) : IsStandardAdditiveCharacter F ψ⁻¹ := by
  obtain ⟨hc, hne, hrat, hnorm⟩ := hψ
  refine ⟨?_, ?_, fun a => ?_, fun a => ?_⟩
  · have : (ψ⁻¹ : AddChar (Adeles F) ℂ) = fun a => ψ (-a) := by
      funext a
      rw [AddChar.inv_apply]
    rw [this]
    exact hc.comp continuous_neg
  · intro h
    apply hne
    rw [← inv_inv ψ, h, inv_one]
  · rw [AddChar.inv_apply, ← map_neg, hrat]
  · rw [AddChar.inv_apply, hnorm]

end Whittaker

end Langlands.Global.RankinSelbergGlobal.Unfolding
