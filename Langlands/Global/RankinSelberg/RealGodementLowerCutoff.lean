import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.TranslateFinite
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Smooth lower compact-picture cutoffs for real Godement sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open GramFormula PrincipalSeriesExtension RealBlockPosition RealJacquetFrobenius
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ

/-- The signed Gram–Schmidt orthogonal factor is smooth on invertible matrices. -/
theorem contDiffOn_signedOrthogonal : ContDiffOn ℝ ∞ (signedOrthogonal : M → M)
    {x | IsUnit x} := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  let fromEntries : (Fin n → Fin n → ℝ) →ₗ[ℝ] M :=
    { toFun := Matrix.of, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  apply fromEntries.toContinuousLinearMap.contDiff.contDiffAt.comp x
  apply contDiffAt_pi.2
  intro i
  apply contDiffAt_pi.2
  intro j
  have hpos (l : ℕ) : 0 < gram l x := by
    simpa only [IsUnit.unit_spec] using gram_pos hx.unit l
  have hRoot (l : ℕ) : ContDiffAt ℝ ∞ (fun y : M => (Real.sqrt (gram l y))⁻¹) x :=
    ((contDiff_gram l).contDiffAt.sqrt (hpos l).ne').inv (Real.sqrt_pos.2 (hpos l)).ne'
  change ContDiffAt ℝ ∞ (fun y : M => gramColumn i j y * (Real.sqrt (gram (i : ℕ) y))⁻¹ *
    (Real.sqrt (gram ((i : ℕ) + 1) y))⁻¹) x
  exact ((contDiff_gramColumn i j).contDiffAt.mul (hRoot i)).mul (hRoot ((i : ℕ) + 1))

/-- A smooth ambient compact-picture function has a smooth induced extension. -/
theorem contMDiff_extension_of_contDiff (s : Fin n → ℂ) {φ : M → ℂ}
    (hφ : ContDiff ℝ ∞ φ) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (extension s (fun κ : K => φ κ.val)) := by
  apply contMDiff_of_contDiffOn
    (ψ := fun x : M => gramExpression s 1 (complexify x) * φ (signedOrthogonal x))
  · exact (contDiffOn_gramExpression s 1).mul
      (hφ.contDiffOn.comp contDiffOn_signedOrthogonal (fun _ _ => Set.mem_univ _))
  · intro g
    rfl

/-- The sum of the squares of the off-diagonal matrix entries. -/
def offDiagonalSquare (x : M) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, x i j ^ 2

theorem contDiff_offDiagonalSquare : ContDiff ℝ ∞ (offDiagonalSquare : M → ℝ) := by
  unfold offDiagonalSquare
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (contDiff_entry i j).pow 2

theorem offDiagonalSquare_nonneg (x : M) : 0 ≤ offDiagonalSquare x :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (x i j)

private theorem offDiagonalSquare_sign_mul (a : Fin n → ℝˣ) (x : M) :
    offDiagonalSquare (Matrix.diagonal (fun i => signReal (a i : ℝ)) * x) =
      offDiagonalSquare x := by
  unfold offDiagonalSquare
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.diagonal_mul, mul_pow, ← sq_abs (signReal (a i : ℝ)), abs_signReal, one_pow, one_mul]

/-- On the orthogonal group the off-diagonal sum of squares vanishes only at
sign matrices. -/
theorem exists_signDiagonal_of_offDiagonalSquare_eq_zero (κ : K)
    (hκ : offDiagonalSquare κ.val = 0) :
    ∃ a : Fin n → ℝˣ, κ = signDiagonal (fun i => (a i : ℝ)) := by
  have hRows : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, κ.val i j ^ 2 = 0 :=
    fun i => (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg fun j _ => sq_nonneg (κ.val a j))).1 hκ i (Finset.mem_univ i)
  have hOff (i j : Fin n) (hij : i ≠ j) : κ.val i j = 0 := by
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (κ.val i k))).1
      (hRows i) j (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
    exact sq_eq_zero_iff.mp hj
  have hDiag : κ.val = Matrix.diagonal (fun i => κ.val i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hOff i j hij]
  have hOrth : κ.val * κ.val.transpose = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp κ.property
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [hDiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal] at hOrth
  have hSq (i : Fin n) : κ.val i i ^ 2 = 1 := by
    simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, pow_two] using
      congrArg (fun A : M => A i i) hOrth
  have hne (i : Fin n) : κ.val i i ≠ 0 := by
    intro h
    have hi := hSq i
    rw [h] at hi
    norm_num at hi
  refine ⟨fun i => Units.mk0 (κ.val i i) (hne i), Subtype.ext ?_⟩
  change κ.val = Matrix.diagonal (fun i => signReal (κ.val i i))
  refine hDiag.trans (congrArg Matrix.diagonal (funext fun i => ?_))
  have hi : κ.val i i = 1 ∨ κ.val i i = -1 := sq_eq_one_iff.mp (hSq i)
  rcases hi with hi | hi <;> rw [hi] <;> norm_num [signReal]

/-- A scalar cutoff of the off-diagonal sum of squares, multiplied by the
monomial giving the required diagonal sign character. -/
def lowerCompactTest (ds : List RealBlock) (b : ℝ → ℝ) (x : M) : ℂ :=
  (b (offDiagonalSquare x) : ℂ) * ∏ i : Fin n, (x i i : ℂ) ^ (realPositionSign ds i).val

private theorem contDiff_lowerCompactTest (ds : List RealBlock) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (lowerCompactTest ds b : M → ℂ) := by
  unfold lowerCompactTest
  apply (Complex.ofRealCLM.contDiff.comp (hb.comp contDiff_offDiagonalSquare)).mul
  exact contDiff_prod fun i _ => (Complex.ofRealCLM.contDiff.comp (contDiff_entry i i)).pow _

private theorem signUnit_character (ds : List RealBlock) (i : ℕ) (a : ℝˣ) :
    realPositionCharacter ds i (signUnit a) =
      ((signReal (a : ℝ) : ℝ) : ℂ) ^ (realPositionSign ds i).val := by
  rw [realPositionCharacter_eq_charFun]
  unfold signUnit signReal
  split_ifs
  · simp [charFun_one]
  · simp [charFun_neg_one]

private theorem lowerCompactTest_sign_mul (ds : List RealBlock) (b : ℝ → ℝ)
    (a : Fin n → ℝˣ) (κ : K) :
    lowerCompactTest ds b ((signDiagonal (fun i => (a i : ℝ)) * κ).val) =
      principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) *
        lowerCompactTest ds b κ.val := by
  have hProd : principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) =
      ∏ i : Fin n, ((signReal (a i : ℝ) : ℝ) : ℂ) ^ (realPositionSign ds i).val := by
    unfold principalSeriesCharacter
    apply Finset.prod_congr rfl
    intro i _
    simp only [Module.finrank_self, pow_one, Real.norm_eq_abs, signUnit_val, abs_signReal,
      Complex.ofReal_one, Complex.one_cpow, mul_one, signUnit_character]
  rw [hProd]
  change lowerCompactTest ds b (Matrix.diagonal (fun i => signReal (a i : ℝ)) * κ.val) = _
  simp only [lowerCompactTest, offDiagonalSquare_sign_mul, Matrix.diagonal_mul,
    Complex.ofReal_mul, mul_pow, Finset.prod_mul_distrib]
  ring

/-- The real position principal-series section induced by the lower compact test. -/
def lowerCutoff (ds : List RealBlock) (b : ℝ → ℝ) : G → ℂ :=
  extension (shiftedExponent n (realPositionExponent ds)) (fun κ : K => lowerCompactTest ds b κ.val)

/-- A smooth cutoff of the off-diagonal sum, with the diagonal parity factors,
extends to a smooth lower principal-series vector for the given positions. -/
def RealGodementLowerCutoffStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (b : ℝ → ℝ), ContDiff ℝ ∞ b →
    lowerCutoff ds b ∈ principalSeries ℝ n (realPositionCharacter ds) ∧
    ∀ κ : Matrix.unitaryGroup (Fin n) ℝ, lowerCutoff ds b (Unitary.toUnits κ) =
      lowerCompactTest ds b κ.val

theorem realGodementLowerCutoff : RealGodementLowerCutoffStatement := by
  intro n ds b hb
  refine ⟨⟨contMDiff_extension_of_contDiff _ (contDiff_lowerCompactTest ds hb), ?_⟩, ?_⟩
  · exact extension_mul_left _ (realPositionCharacter_eq_signUnit_mul ds)
      (lowerCompactTest_sign_mul ds b)
  · exact extension_unitary _ _

/-- A polynomial angular test has a K-finite lower position section. -/
theorem lowerCutoff_polynomial_mem_kFiniteFunctions (ds : List RealBlock) (p : Polynomial ℝ) :
    lowerCutoff ds p.eval ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds))
      (unitaryCompact ℝ n) := by
  classical
  let A := MvPolynomial (Fin n × Fin n) ℂ
  let Q : A := ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, MvPolynomial.X (i, j) ^ 2
  let C : ℝ →+* A := (MvPolynomial.C : ℂ →+* A).comp Complex.ofRealHom
  let P : A := p.eval₂ C Q * ∏ i : Fin n, MvPolynomial.X (i, i) ^ (realPositionSign ds i).val
  have hP (κ : K) : lowerCompactTest ds p.eval κ.val =
      MvPolynomial.eval (fun ij => (κ.val ij.1 ij.2 : ℂ)) P := by
    let e : A →+* ℂ := MvPolynomial.eval (fun ij => (κ.val ij.1 ij.2 : ℂ))
    have hX (ij : Fin n × Fin n) : e (MvPolynomial.X ij) = (κ.val ij.1 ij.2 : ℂ) :=
      MvPolynomial.eval_X ij
    have hQ : e Q = (offDiagonalSquare κ.val : ℂ) := by
      simp only [Q, offDiagonalSquare, map_sum, map_pow, hX, Complex.ofReal_sum, Complex.ofReal_pow]
    have hC : e.comp C = Complex.ofRealHom := by
      ext x
      change e (MvPolynomial.C (Complex.ofRealHom x)) = Complex.ofRealHom x
      exact MvPolynomial.eval_C _
    have hAngle : e (p.eval₂ C Q) = ((p.eval (offDiagonalSquare κ.val) : ℝ) : ℂ) := by
      rw [Polynomial.hom_eval₂, hC, hQ]
      exact Polynomial.eval₂_hom Complex.ofRealHom _
    change lowerCompactTest ds p.eval κ.val = e P
    simp only [P, map_mul, map_prod, map_pow, hX, hAngle, lowerCompactTest]
  have hp : ContDiff ℝ ∞ p.eval := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
      using p.contDiff_aeval (𝕜 := ℝ) ∞
  have hFin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K =>
      fun κ : K => lowerCompactTest ds p.eval (κ * k).val)) := by
    have hEq : (fun k κ : K => lowerCompactTest ds p.eval (κ * k).val) =
        fun k κ : K => MvPolynomial.eval (fun ij => ((κ * k).val ij.1 ij.2 : ℂ)) P := by
      funext k κ
      exact hP (κ * k)
    rw [hEq]
    exact TranslateFinite.finiteDimensional_span_eval P
  exact extension_mem_kFiniteFunctions _ (realPositionCharacter_eq_signUnit_mul ds)
    ((contDiff_lowerCompactTest ds hp).continuous.comp continuous_subtype_val) hFin
    (lowerCompactTest_sign_mul ds p.eval)

end Langlands.Global.RankinSelbergGlobal.RealGodement
