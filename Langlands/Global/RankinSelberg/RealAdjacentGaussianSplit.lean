import Langlands.Global.RankinSelberg.RealGodementGaussianPolynomial
import Langlands.Global.RankinSelberg.RealGodementColumnProduct
import Langlands.Global.RankinSelberg.RealGodementFourierCovariance
import Langlands.Global.RankinSelberg.RealTriangularInversion

/-! # Splitting real polynomial Gaussian tests at the last column

See the paired Markdown file.
-/

noncomputable section

open scoped Matrix.Norms.Operator SchwartzMap
open MvPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open Langlands.Archimedean (unitaryCompact)
open RealGodementGaussianPolynomial
open RealGodement (realRectangularSchwartzFourier rectangularTranslate)

/-! ### Left orthogonal translates of polynomial Gaussian tests -/

section Left

variable {m n : ℕ}

/-- Left multiplication by an orthogonal matrix preserves the sum of squares. -/
theorem matrixSqNorm_orthogonal_mul (A : Matrix (Fin m) (Fin n) ℝ)
    {g : Langlands.GeneralLinear m ℝ} (hg : g ∈ unitaryCompact ℝ m) :
    matrixSqNorm (g.val * A) = matrixSqNorm A := by
  have hk : g.val.transpose * g.val = 1 := by
    have h := Unitary.star_mul_self_of_mem hg
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using h
  have htrace (B : Matrix (Fin m) (Fin n) ℝ) : matrixSqNorm B = Matrix.trace (B.transpose * B) := by
    simp only [matrixSqNorm, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      sq]
    rw [Finset.sum_comm]
  rw [htrace, htrace, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc g.val.transpose,
    hk, Matrix.one_mul]

private def entryLinear' (v : Coordinates m n) : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun A := A v.1 v.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem totalDegree_bind₁_le' {ι κ : Type*} (f : ι → MvPolynomial κ ℂ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial ι ℂ) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun d hd => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans
    (le_totalDegree hd))
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))

/-- Left multiplication by an orthogonal matrix acts on polynomial Gaussian tests by a linear
substitution in the entries, which does not raise the total degree. -/
theorem exists_leftTranslate_gaussianPolynomial (p : MvPolynomial (Coordinates m n) ℂ)
    {g : Langlands.GeneralLinear m ℝ} (hg : g ∈ unitaryCompact ℝ m) :
    ∃ q ∈ restrictTotalDegree (Coordinates m n) ℂ p.totalDegree,
      ∀ A, gaussianPolynomial p (g.val * A) = gaussianPolynomial q A := by
  let L (v : Coordinates m n) : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    (entryLinear' v).comp (_root_.mulLeftLinearMap (Fin n) ℝ g.val)
  let q (v : Coordinates m n) := realLinearPolynomial (L v)
  refine ⟨bind₁ q p, (mem_restrictTotalDegree _ _ _).mpr
    (totalDegree_bind₁_le' q (fun v => totalDegree_realLinearPolynomial _) p), fun A => ?_⟩
  rw [gaussianPolynomial_apply, gaussianPolynomial_apply, matrixGaussian, matrixGaussian,
    matrixSqNorm_orthogonal_mul A hg]
  congr 1
  change aeval (coordinates (g.val * A)) p = aeval (coordinates A) (bind₁ q p)
  rw [aeval_bind₁]
  have hq (v : Coordinates m n) : aeval (coordinates A) (q v) = coordinates (g.val * A) v :=
    eval_realLinearPolynomial (L v) A
  simp_rw [hq]

/-- The left orthogonal translates of a polynomial Gaussian test span a finite-dimensional
space of functions. -/
theorem finiteDimensional_gaussianPolynomial_left {K : Type*} [Group K]
    (iK : K →* Langlands.GeneralLinear m ℝ) (hmem : ∀ k, iK k ∈ unitaryCompact ℝ m)
    (p : MvPolynomial (Coordinates m n) ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K =>
      fun X : Matrix (Fin m) (Fin n) ℝ => gaussianPolynomial p (((iK k)⁻¹).val * X))) := by
  let T : MvPolynomial (Coordinates m n) ℂ →ₗ[ℂ] (Matrix (Fin m) (Fin n) ℝ → ℂ) :=
    { toFun := fun q => gaussianPolynomial q
      map_add' := fun q q' => by rw [gaussianPolynomial_add]; rfl
      map_smul' := fun c q => by rw [gaussianPolynomial_smul]; rfl }
  let R := (restrictTotalDegree (Coordinates m n) ℂ p.totalDegree).map T
  have : FiniteDimensional ℂ (restrictTotalDegree (Coordinates m n) ℂ p.totalDegree) :=
    inferInstance
  have hR : FiniteDimensional ℂ R := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := R)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  have hinv : (iK k)⁻¹ ∈ unitaryCompact ℝ m := (unitaryCompact ℝ m).inv_mem (hmem k)
  obtain ⟨q, hq, hA⟩ := exists_leftTranslate_gaussianPolynomial p hinv
  exact ⟨q, hq, funext fun X => (hA X).symm⟩

end Left

/-! ### Fourier transforms of tests whose orthogonal translates span a finite-dimensional space -/

section Fourier

variable {m : ℕ}

/-- If the left orthogonal translates of a square Schwartz test span a finite-dimensional space,
so do those of its real square Fourier transform. -/
theorem finiteDimensional_fourier_left {K : Type*} [Group K]
    (iK : K →* Langlands.GeneralLinear m ℝ) (hmem : ∀ k, iK k ∈ unitaryCompact ℝ m)
    (b : ℝˣ) (F : 𝓢(Matrix (Fin m) (Fin m) ℝ, ℂ))
    (hF : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K =>
      fun X : Matrix (Fin m) (Fin m) ℝ => F (((iK k)⁻¹).val * X)))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K =>
      fun X : Matrix (Fin m) (Fin m) ℝ => realRectangularSchwartzFourier b F (((iK k)⁻¹).val * X))) := by
  let coe : 𝓢(Matrix (Fin m) (Fin m) ℝ, ℂ) →ₗ[ℂ] (Matrix (Fin m) (Fin m) ℝ → ℂ) :=
    { toFun := fun Ψ => Ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcoe : Function.Injective coe := fun Ψ Ψ' h => SchwartzMap.ext (congrFun h)
  let T : 𝓢(Matrix (Fin m) (Fin m) ℝ, ℂ) →ₗ[ℂ] (Matrix (Fin m) (Fin m) ℝ → ℂ) :=
    { toFun := fun Ψ => realRectangularSchwartzFourier b Ψ
      map_add' := fun Ψ Ψ' => by
        simp only [realRectangularSchwartzFourier, RealGodement.scaledEuclideanFourier, map_add]
        rfl
      map_smul' := fun c Ψ => by
        simp only [realRectangularSchwartzFourier, RealGodement.scaledEuclideanFourier, map_smul,
          RingHom.id_apply]
        rfl }
  let tr (k : K) : 𝓢(Matrix (Fin m) (Fin m) ℝ, ℂ) := rectangularTranslate (iK k)⁻¹ 1 F
  let S := Submodule.span ℂ (Set.range tr)
  have hS : FiniteDimensional ℂ S := by
    have hmap : S.map coe = Submodule.span ℂ (Set.range fun k : K =>
        fun X : Matrix (Fin m) (Fin m) ℝ => F (((iK k)⁻¹).val * X)) := by
      have hfun : (⇑coe ∘ tr) = fun k X => F (((iK k)⁻¹).val * X) := by
        funext k X
        change rectangularTranslate (iK k)⁻¹ 1 F X = _
        rw [RealGodement.rectangularTranslate_apply, Units.val_one, Matrix.mul_one]
      rw [Submodule.map_span, ← Set.range_comp, hfun]
    have : FiniteDimensional ℂ (S.map coe) := hmap ▸ hF
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective coe hcoe S).symm
  apply Submodule.finiteDimensional_of_le (S₂ := S.map T)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  refine ⟨tr k, Submodule.subset_span ⟨k, rfl⟩, funext fun X => ?_⟩
  have hinv : (iK k)⁻¹ ∈ unitaryCompact ℝ m := (unitaryCompact ℝ m).inv_mem (hmem k)
  have hcov := RealGodement.realGodementFourierCovariance m m b (iK k)⁻¹ 1 F X
  have hdet : |((iK k)⁻¹).val.det| = 1 :=
    Langlands.Archimedean.MaximalParabolicIntegration.abs_det_unitary ⟨_, hinv⟩
  have hι : Langlands.GeneralLinear.inverseTranspose m ℝ (iK k)⁻¹ = (iK k)⁻¹ :=
    GodementJacquet.realInverseTranspose_unitary_eq m ⟨_, hinv⟩
  change realRectangularSchwartzFourier b (rectangularTranslate (iK k)⁻¹ 1 F) X = _
  rw [hcov, hdet, hι, map_one]
  simp only [Units.val_one, Matrix.det_one, abs_one, one_pow, mul_one, inv_one,
    Complex.ofReal_one, one_mul]

end Fourier

/-! ### Splitting Gaussian monomials at the last column -/

section Split

variable {r : ℕ}

private theorem eval_monomial_fintype' {ι : Type*} [Fintype ι] (c : ι → ℂ) (d : ι →₀ ℕ) (a : ℂ) :
    eval c (monomial d a) = a * ∏ i, c i ^ d i := by
  rw [eval_monomial, Finsupp.prod_fintype]
  exact fun i => pow_zero (c i)

/-- Column vectors as one-column matrices. -/
def columnMatrixEquiv (n : ℕ) : (Fin n → ℝ) ≃L[ℝ] Matrix (Fin n) (Fin 1) ℝ :=
  (LinearEquiv.piCongrRight fun _ : Fin n =>
    (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm).toContinuousLinearEquiv

@[simp] theorem columnMatrixEquiv_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) (j : Fin 1) :
    columnMatrixEquiv n x i j = x i := rfl

/-- A monomial in the entries of a column vector times its Gaussian `exp(-∑ xᵢ²)`. -/
def columnGaussianMonomial (d : Fin (r + 1) → ℕ) : 𝓢(Fin (r + 1) → ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (columnMatrixEquiv (r + 1))
    (gaussianPolynomial (monomial (Finsupp.equivFunOnFinite.symm
      fun v : Coordinates (r + 1) 1 => d v.1) (1 : ℂ)))

theorem columnGaussianMonomial_apply (d : Fin (r + 1) → ℕ) (x : Fin (r + 1) → ℝ) :
    columnGaussianMonomial d x =
      (∏ i, (x i : ℂ) ^ d i) * (Real.exp (-∑ i, x i ^ 2) : ℂ) := by
  change gaussianPolynomial _ (columnMatrixEquiv (r + 1) x) = _
  rw [gaussianPolynomial_apply, eval_monomial_fintype', one_mul, matrixGaussian]
  congr 1
  · rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_one]
    rfl
  · congr 3
    unfold matrixSqNorm
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_one]
    rfl

/-- The exponents of a rectangular monomial restricted to its leading square block. -/
def leadingExponents (d : Coordinates (r + 1) (r + 2) →₀ ℕ) : Coordinates (r + 1) (r + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => d (v.1, v.2.castSucc)

/-- A Gaussian monomial on `(r + 1) × (r + 2)` matrices is the separated product of the leading
square Gaussian monomial and a column Gaussian monomial. -/
theorem gaussianMonomial_eq_realColumnProduct (d : Coordinates (r + 1) (r + 2) →₀ ℕ) (a : ℂ) :
    gaussianPolynomial (monomial d a) =
      realColumnProduct (gaussianPolynomial (monomial (leadingExponents d) a))
        (columnGaussianMonomial fun i => d (i, Fin.last (r + 1))) := by
  apply SchwartzMap.ext
  intro B
  rw [realColumnProduct_apply, gaussianPolynomial_apply, gaussianPolynomial_apply,
    columnGaussianMonomial_apply, eval_monomial_fintype', eval_monomial_fintype']
  have hnorm : matrixSqNorm B = matrixSqNorm (leadingColumns B) +
      ∑ i, lastColumn B i ^ 2 := by
    unfold matrixSqNorm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_castSucc]
    rfl
  have hprod : (∏ v, coordinates B v ^ d v) =
      (∏ v, coordinates (leadingColumns B) v ^ leadingExponents d v) *
        (∏ i, (lastColumn B i : ℂ) ^ d (i, Fin.last (r + 1))) := by
    simp only [Fintype.prod_prod_type]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_castSucc]
    rfl
  rw [hprod, matrixGaussian, matrixGaussian, hnorm, neg_add, Real.exp_add, Complex.ofReal_mul]
  ring

/-- A polynomial Gaussian test is the sum of its monomial Gaussian tests. -/
theorem gaussianPolynomial_sum_monomials {m n : ℕ} (p : MvPolynomial (Coordinates m n) ℂ) :
    gaussianPolynomial p = ∑ u ∈ p.support, gaussianPolynomial (monomial u (p.coeff u)) := by
  change gaussianPolynomialLinear m n p =
    ∑ u ∈ p.support, gaussianPolynomialLinear m n (monomial u (p.coeff u))
  rw [← map_sum, ← p.as_sum]

end Split

end Langlands.Global.RankinSelbergGlobal.RealJacquet
