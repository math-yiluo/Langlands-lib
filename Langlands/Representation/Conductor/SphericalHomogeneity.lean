import Langlands.Representation.Conductor.SphericalPolynomial

/-!
# Integral homogeneity of the spherical Whittaker polynomial
-/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial Langlands.GeneralLinear Langlands.GeneralLinear.Spherical
open scoped BigOperators

universe uK uσ uF uΓ

section Scalar

variable {K : Type uK} [Field K]

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (c : Kˣ) (a : ι → ℤ) :
    (∏ i ∈ s, (c : K) ^ a i) = (c : K) ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ c.ne_zero]

/-- Complete homogeneous symmetric polynomials have their indicated degree. -/
theorem hsymm_eval_scale {σ : Type uσ} [Fintype σ] [DecidableEq σ]
    (c : K) (x : σ → K) (k : ℕ) :
    eval (fun i => c * x i) (hsymm σ K k) =
      c ^ k * eval x (hsymm σ K k) := by
  simp only [hsymm, map_sum, ← Multiset.prod_hom', eval_X]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Multiset.prod_map_mul]
  simp only [Multiset.map_const', Multiset.prod_replicate, s.2]

/-- The negative-index convention is compatible with scaling by units. -/
theorem completeSymm_eval_scale {σ : Type uσ} [Fintype σ] [DecidableEq σ]
    (c : Kˣ) (x : σ → K) (k : ℤ) :
    eval (fun i => (c : K) * x i) (completeSymm σ K k) =
      (c : K) ^ k * eval x (completeSymm σ K k) := by
  unfold completeSymm
  split_ifs with hk
  · rw [hsymm_eval_scale, ← Int.toNat_of_nonneg hk]
    simp only [Int.toNat_natCast, zpow_natCast]
  · simp

/-- Row and column factors in Jacobi--Trudi cancel the index contributions. -/
theorem jacobiTrudi_eval_scale {m : ℕ}
    (c : Kˣ) (x : Fin m → K) (a : Fin m → ℤ) :
    eval (fun i => (c : K) * x i) (jacobiTrudi K a) =
      (c : K) ^ (∑ i, a i) * eval x (jacobiTrudi K a) := by
  let A : Matrix (Fin m) (Fin m) K :=
    fun i j => eval x (completeSymm (Fin m) K (a i - i + j))
  have hmat :
      (fun i j : Fin m =>
        eval (fun k => (c : K) * x k) (completeSymm (Fin m) K (a i - i + j))) =
      (fun i j : Fin m => (c : K) ^ (a i - i) * ((c : K) ^ (j : ℤ) * A i j)) := by
    apply Matrix.ext
    intro i j
    rw [completeSymm_eval_scale, zpow_add₀ c.ne_zero]
    dsimp [A]
    ring
  simp only [jacobiTrudi, RingHom.map_det]
  change Matrix.det (fun i j : Fin m =>
    eval (fun k => (c : K) * x k) (completeSymm (Fin m) K (a i - i + j))) =
      (c : K) ^ (∑ i, a i) * A.det
  rw [hmat]
  erw [Matrix.det_mul_column (fun i : Fin m => (c : K) ^ (a i - i))
    (fun i j => (c : K) ^ (j : ℤ) * A i j),
    Matrix.det_mul_row (fun j : Fin m => (c : K) ^ (j : ℤ)) A,
    prod_zpow_eq_zpow_sum, prod_zpow_eq_zpow_sum]
  rw [← mul_assoc, ← zpow_add₀ c.ne_zero, Finset.sum_sub_distrib, sub_add_cancel]

/-- An integral-weight Schur function scales by the sum of all its weights. -/
theorem satakeSchur_scale {n : ℕ}
    (c : ℂˣ) (x : Fin (n + 1) → ℂˣ) (lam : Fin (n + 1) → ℤ) :
    satakeSchur (fun i => c * x i) lam =
      (c : ℂ) ^ (∑ i, lam i) * satakeSchur x lam := by
  unfold satakeSchur
  simp only [Units.val_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [mul_zpow, jacobiTrudi_eval_scale]
  rw [← zpow_natCast, ← zpow_mul]
  have hexp :
      ((n + 1 : ℕ) : ℤ) * lam (Fin.last n) +
        ∑ i : Fin (n + 1), (lam i - lam (Fin.last n)) = ∑ i, lam i := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  calc
    _ = ((c : ℂ) ^ (((n + 1 : ℕ) : ℤ) * lam (Fin.last n)) *
        (c : ℂ) ^ (∑ i, (lam i - lam (Fin.last n)))) *
        ((∏ i, (x i : ℂ)) ^ lam (Fin.last n) *
          eval (fun i => (x i : ℂ))
            (jacobiTrudi ℂ (fun i => lam i - lam (Fin.last n)))) := by ring
    _ = _ := by rw [← zpow_add₀ c.ne_zero, hexp]

end Scalar

section Laurent

variable (σ : Type uσ) (K : Type uK) [Fintype σ] [Field K]

/-- Simultaneous scaling of all Laurent coordinates by a unit. -/
def torusPolynomialScale (c : Kˣ) :
    TorusPolynomialAlgebra σ K →ₐ[K] TorusPolynomialAlgebra σ K :=
  IsLocalization.Away.liftAlgHom (∏ i : σ, (X i : MvPolynomial σ K))
    (f := aeval (fun i =>
      algebraMap K (TorusPolynomialAlgebra σ K) (c : K) *
        algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i))) (by
      simp only [map_prod, aeval_X, Finset.prod_mul_distrib, Finset.prod_const]
      rw [← map_prod]
      exact ((c.isUnit.map (algebraMap K (TorusPolynomialAlgebra σ K))).pow
        (Fintype.card σ)).mul (IsLocalization.Away.algebraMap_isUnit _))

@[simp] theorem torusPolynomialScale_algebraMap (c : Kˣ) (p : MvPolynomial σ K) :
    torusPolynomialScale σ K c
      (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) p) =
      aeval (fun i =>
        algebraMap K (TorusPolynomialAlgebra σ K) (c : K) *
          algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i)) p := by
  simp [torusPolynomialScale, IsLocalization.Away.liftAlgHom]

theorem torusPolynomialScale_commute (c : Kˣ) (e : Equiv.Perm σ) :
    (torusPolynomialScale σ K c).comp (torusPolynomialPermutation σ K e) =
      (torusPolynomialPermutation σ K e).comp (torusPolynomialScale σ K c) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (∏ i : σ, (X i : MvPolynomial σ K)))
  ext i
  change torusPolynomialScale σ K c (torusPolynomialPermutation σ K e
    (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i))) =
      torusPolynomialPermutation σ K e (torusPolynomialScale σ K c
        (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i)))
  simp only [torusPolynomialPermutation_algebraMap, rename_X,
    torusPolynomialScale_algebraMap, aeval_X, map_mul, AlgHom.commutes]

theorem torusPolynomialEvaluation_scale (c : Kˣ) (x : σ → Kˣ)
    (p : TorusPolynomialAlgebra σ K) :
    torusPolynomialEvaluation σ K x (torusPolynomialScale σ K c p) =
      torusPolynomialEvaluation σ K (fun i => c * x i) p := by
  have h : (torusPolynomialEvaluation σ K x).comp (torusPolynomialScale σ K c) =
      torusPolynomialEvaluation σ K (fun i => c * x i) := by
    apply IsLocalization.algHom_ext (Submonoid.powers (∏ i : σ, (X i : MvPolynomial σ K)))
    ext i
    change torusPolynomialEvaluation σ K x (torusPolynomialScale σ K c
      (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i))) =
        torusPolynomialEvaluation σ K (fun i => c * x i)
          (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i))
    simp only [torusPolynomialScale_algebraMap, aeval_X, map_mul, AlgHom.commutes,
      torusPolynomialEvaluation_algebraMap, Algebra.algebraMap_self,
      RingHom.id_apply, Units.val_mul]
  exact DFunLike.congr_fun h p

/-- Simultaneous scaling preserves the symmetric Laurent subalgebra. -/
def symmetricTorusScale (c : Kˣ) :
    symmetricTorusSubalgebra σ K →ₐ[K] symmetricTorusSubalgebra σ K where
  toFun p := ⟨torusPolynomialScale σ K c p.val, fun e => by
    have h := DFunLike.congr_fun (torusPolynomialScale_commute σ K c e) p.val
    simp only [AlgHom.comp_apply] at h
    change torusPolynomialPermutation σ K e (torusPolynomialScale σ K c p.val) = _
    rw [← h, p.property e]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' p r := Subtype.ext (map_mul _ p.val r.val)
  map_zero' := Subtype.ext (map_zero _)
  map_add' p r := Subtype.ext (map_add _ p.val r.val)
  commutes' a := Subtype.ext ((torusPolynomialScale σ K c).commutes a)

@[simp] theorem symmetricTorusEvaluation_scale (c : Kˣ) (x : σ → Kˣ)
    (p : symmetricTorusSubalgebra σ K) :
    symmetricTorusEvaluation σ K x (symmetricTorusScale σ K c p) =
      symmetricTorusEvaluation σ K (fun i => c * x i) p :=
  torusPolynomialEvaluation_scale σ K c x p.val

/-- Integral homogeneity in the simultaneous scaling of the Laurent variables. -/
def IsSymmetricTorusHomogeneous
    (p : symmetricTorusSubalgebra σ K) (d : ℤ) : Prop :=
  ∀ c : Kˣ, symmetricTorusScale σ K c p =
    algebraMap K (symmetricTorusSubalgebra σ K) ((c : K) ^ d) * p

end Laurent

theorem symmetricTorusScale_schur {n : ℕ}
    (c : ℂˣ) (lam : Fin (n + 1) → ℤ) :
    symmetricTorusScale (Fin (n + 1)) ℂ c (symmetricTorusSchur ℂ lam) =
      algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
        ((c : ℂ) ^ (∑ i, lam i)) * symmetricTorusSchur ℂ lam := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_scale, symmetricTorusEvaluation_schur,
    map_mul, AlgHom.commutes, symmetricTorusEvaluation_schur]
  exact satakeSchur_scale c x lam

theorem symmetricTorusSchur_isHomogeneous {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    IsSymmetricTorusHomogeneous (Fin (n + 1)) ℂ
      (symmetricTorusSchur ℂ lam) (∑ i, lam i) :=
  fun c => symmetricTorusScale_schur c lam

section SphericalFunction

open Iwasawa

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement v ϖ)
  (θ : upperUnipotent (n + 1) F →* ℂˣ) (q : ℕ)

/-- The Laurent-valued spherical formula is homogeneous of the sum of its
Iwasawa exponents. -/
theorem sphericalWhittakerPolynomial_scale
    (c : ℂˣ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    symmetricTorusScale (Fin (n + 1)) ℂ c
      (sphericalWhittakerPolynomial hϖ θ q g) =
      algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
        ((c : ℂ) ^ (∑ i, exponent hϖ g i)) *
          sphericalWhittakerPolynomial hϖ θ q g := by
  classical
  unfold sphericalWhittakerPolynomial
  split_ifs
  · rw [map_mul, AlgHom.commutes, symmetricTorusScale_schur]
    ring
  · rw [map_zero, mul_zero]

theorem sphericalWhittakerPolynomial_isHomogeneous
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    IsSymmetricTorusHomogeneous (Fin (n + 1)) ℂ
      (sphericalWhittakerPolynomial hϖ θ q g) (∑ i, exponent hϖ g i) :=
  fun c => sphericalWhittakerPolynomial_scale hϖ θ q c g

end SphericalFunction

end Langlands.Conductor
