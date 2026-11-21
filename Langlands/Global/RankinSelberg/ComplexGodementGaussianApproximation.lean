import Langlands.Global.RankinSelberg.ComplexGodementGaussianPolynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization

/-! # Uniform approximation of compact tests with a Gaussian error bound -/

noncomputable section

open scoped Matrix.Norms.Operator SchwartzMap ZeroAtInfty OnePoint
open Filter MvPolynomial Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial

variable {m n : ℕ}

private abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ
private abbrev Variables (m n : ℕ) := Option (Coordinates m n)

private def generatorPoly : Variables m n → MvPolynomial (Coordinates m n) ℂ
  | none => 1
  | some i => X i

private def generator (v : Variables m n) : C(OnePoint (Mat m n), ℂ) :=
  (gaussianPolynomial (generatorPoly v)).toZeroAtInfty.toOnePoint

private theorem generator_coe (v : Variables m n) (A : Mat m n) :
    generator v (A : OnePoint (Mat m n)) =
      eval (coordinates A) (generatorPoly v) * matrixGaussian A := by
  exact gaussianPolynomial_apply _ _

private theorem generator_infty (v : Variables m n) :
    generator v (∞ : OnePoint (Mat m n)) = 0 := rfl

private theorem generator_star (v : Variables m n) :
    star (generator v) = generator v := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp [generator_infty]
  | coe A =>
      rw [ContinuousMap.star_apply, generator_coe]
      cases v with
      | none =>
          simp only [generatorPoly, map_one, one_mul, matrixGaussian, Complex.star_def, Complex.conj_ofReal]
      | some v =>
          rcases v with ⟨i, j, b⟩
          cases b
          · simp only [generatorPoly, eval_X, coordinates_re, matrixGaussian, star_mul,
              Complex.star_def, Complex.conj_ofReal]
            exact mul_comm _ _
          · simp only [generatorPoly, eval_X, coordinates_im, matrixGaussian, star_mul,
              Complex.star_def, Complex.conj_ofReal]
            exact mul_comm _ _

private def testAlgebra (m n : ℕ) : StarSubalgebra ℂ C(OnePoint (Mat m n), ℂ) where
  toSubalgebra := (aeval (generator : Variables m n → C(OnePoint (Mat m n), ℂ))).range
  star_mem' := by
    rintro _ ⟨p, rfl⟩
    refine ⟨map (starRingEnd ℂ) p, ?_⟩
    induction p using MvPolynomial.induction_on with
    | C c =>
        ext x
        simp [smul_eq_mul]
    | add p q hp hq => simp only [map_add, star_add, hp, hq]
    | mul_X p i hp =>
        simp only [map_mul, MvPolynomial.map_X, star_mul, hp]
        rw [show (aeval generator).toRingHom (X i) = generator i from aeval_X _ _, generator_star, mul_comm]

private theorem generator_mem (v : Variables m n) : generator v ∈ testAlgebra m n :=
  ⟨X v, aeval_X _ _⟩

private theorem matrixGaussian_ne_zero (A : Mat m n) : matrixGaussian A ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

private theorem testAlgebra_separatesPoints (m n : ℕ) : (testAlgebra m n).SeparatesPoints := by
  intro x y hxy
  by_contra! he
  have hgen (v : Variables m n) : generator v x = generator v y :=
    he _ ⟨generator v, generator_mem v, rfl⟩
  induction x using OnePoint.rec with
  | infty =>
      induction y using OnePoint.rec with
      | infty => exact hxy rfl
      | coe B =>
          have hz := hgen none
          rw [generator_infty, generator_coe, show generatorPoly (none : Variables m n) = 1 from rfl,
            map_one, one_mul] at hz
          exact matrixGaussian_ne_zero B hz.symm
  | coe A =>
      induction y using OnePoint.rec with
      | infty =>
          have hz := hgen none
          rw [generator_infty, generator_coe, show generatorPoly (none : Variables m n) = 1 from rfl,
            map_one, one_mul] at hz
          exact matrixGaussian_ne_zero A hz
      | coe B =>
          have hG : matrixGaussian A = matrixGaussian B := by
            simpa only [generator_coe, generatorPoly, map_one, one_mul] using hgen none
          have hcoord (i : Coordinates m n) : coordinates A i = coordinates B i := by
            have hi := hgen (some i)
            simp only [generator_coe, generatorPoly, eval_X, hG] at hi
            exact mul_right_cancel₀ (matrixGaussian_ne_zero B) hi
          apply hxy
          congr 1
          ext i j
          exact Complex.ext (Complex.ofReal_injective (hcoord (i, j, false)))
            (Complex.ofReal_injective (hcoord (i, j, true)))

private theorem exists_powerSum (p : MvPolynomial (Variables m n) ℂ) :
    ∃ (l : ℕ) (k : Fin l → ℕ) (q : Fin l → MvPolynomial (Coordinates m n) ℂ),
      ∀ A : Mat m n, matrixGaussian A * (aeval generator p) (A : OnePoint (Mat m n)) =
        ∑ j, eval (coordinates A) (q j) * matrixGaussian A ^ (k j + 1) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      exact ⟨1, fun _ => 0, fun _ => C c, by simp [mul_comm]⟩
  | add p q hp hq =>
      obtain ⟨l, k, P, hP⟩ := hp
      obtain ⟨l', k', Q, hQ⟩ := hq
      refine ⟨l + l', Fin.addCases k k', Fin.addCases P Q, fun A => ?_⟩
      rw [map_add, ContinuousMap.add_apply, mul_add, hP, hQ, Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
  | mul_X p v hp =>
      obtain ⟨l, k, q, hq⟩ := hp
      refine ⟨l, fun j => k j + 1, fun j => q j * generatorPoly v, fun A => ?_⟩
      rw [map_mul, aeval_X, ContinuousMap.mul_apply, ← mul_assoc, hq, generator_coe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, pow_succ]
      ring

private theorem compact_div_gaussian_hasCompactSupport {f : Mat m n → ℂ}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun A => f A / matrixGaussian A) := by
  refine HasCompactSupport.of_support_subset_isCompact hf fun A hA => subset_tsupport _ ?_
  exact fun hz => hA (by simp [hz])

/-- A polynomial times a positive integral Gaussian power is a dilated Gaussian-polynomial
test. The polynomial reparametrizes the coordinates by the inverse dilation. -/
theorem exists_gaussianPolynomial_dilation (p : MvPolynomial (Coordinates m n) ℂ) (k : ℕ) :
    ∃ (z : ℂˣ) (q : MvPolynomial (Coordinates m n) ℂ), ∀ A : Mat m n,
      gaussianPolynomial q ((z : ℂ) • A) = eval (coordinates A) p * matrixGaussian A ^ (k + 1) := by
  let b := Real.sqrt ((k + 1 : ℕ) : ℝ)
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  let z := Units.mk0 (b : ℂ) hb'
  let q := bind₁ (fun i => C (b : ℂ)⁻¹ * X i) p
  refine ⟨z, q, fun A => ?_⟩
  have hcoord (i : Coordinates m n) :
      coordinates ((z : ℂ) • A) i = (b : ℂ) * coordinates A i := by
    change coordinatePartCLM i.2.2 ((b : ℂ) * A i.1 i.2.1) = _
    rw [← Complex.real_smul, (coordinatePartCLM _).map_smul, Complex.real_smul]
    rfl
  have hEval : eval (coordinates ((z : ℂ) • A)) q = eval (coordinates A) p := by
    have hVar (i : Coordinates m n) :
        aeval (coordinates ((z : ℂ) • A)) (C (b : ℂ)⁻¹ * X i) = coordinates A i := by
      change eval (coordinates ((z : ℂ) • A)) (C (b : ℂ)⁻¹ * X i) = _
      rw [map_mul, eval_C, eval_X, hcoord, ← mul_assoc, inv_mul_cancel₀ hb', one_mul]
    change aeval (coordinates ((z : ℂ) • A)) q = aeval (coordinates A) p
    simp only [q, aeval_bind₁, hVar]
  have hnorm : ‖(z : ℂ)‖ ^ 2 = ((k + 1 : ℕ) : ℝ) := by
    change ‖(b : ℂ)‖ ^ 2 = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, Real.sq_sqrt (by positivity)]
  have hSq : matrixSqNorm ((z : ℂ) • A) = ((k + 1 : ℕ) : ℝ) * matrixSqNorm A := by
    simp only [matrixSqNorm, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, hnorm,
      ← Finset.mul_sum]
  rw [gaussianPolynomial_apply, hEval]
  simp only [matrixGaussian, hSq, ← mul_neg, Real.exp_nat_mul, Complex.ofReal_pow]

/-- Compactly supported continuous tests approximate by finite sums of positive powers
of the Gaussian times polynomials, with a pointwise error bounded by a fixed Gaussian. -/
def ComplexGodementGaussianApproximationStatement : Prop :=
  ∀ (m n : ℕ) (f : Mat m n → ℂ), Continuous f → HasCompactSupport f →
    ∀ ε : ℝ, 0 < ε →
      ∃ (l : ℕ) (k : Fin l → ℕ) (q : Fin l → MvPolynomial (Coordinates m n) ℂ),
        ∀ A : Mat m n,
          ‖f A - ∑ j, eval (coordinates A) (q j) * matrixGaussian A ^ (k j + 1)‖ ≤
            ε * ‖matrixGaussian A‖

theorem complexGodementGaussianApproximation : ComplexGodementGaussianApproximationStatement := by
  intro m n f hf hfC ε hε
  have hGc : Continuous (matrixGaussian (m := m) (n := n)) := by
    have he : (gaussianPolynomial (1 : MvPolynomial (Coordinates m n) ℂ) : Mat m n → ℂ) =
        matrixGaussian := by
      funext A
      simp
    exact he ▸ (gaussianPolynomial (1 : MvPolynomial (Coordinates m n) ℂ)).continuous
  let f₀ : C₀(Mat m n, ℂ) :=
    ⟨⟨fun A => f A / matrixGaussian A, hf.div hGc matrixGaussian_ne_zero⟩, by
      have hz := (hasCompactSupport_iff_eventuallyEq.mp
        (compact_div_gaussian_hasCompactSupport hfC))
      rw [coclosedCompact_eq_cocompact] at hz
      exact tendsto_const_nhds.congr' hz.symm⟩
  let F := f₀.toOnePoint
  let A := testAlgebra m n
  have hA : A.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A
      (testAlgebra_separatesPoints m n)
  have hF : F ∈ closure (A : Set C(OnePoint (Mat m n), ℂ)) := by
    change F ∈ A.topologicalClosure
    rw [hA]
    trivial
  obtain ⟨P, hP, hdist⟩ := Metric.mem_closure_iff.mp hF ε hε
  obtain ⟨p, rfl⟩ : ∃ p, aeval generator p = P := hP
  obtain ⟨l, k, q, heval⟩ := exists_powerSum p
  refine ⟨l, k, q, fun X => ?_⟩
  rw [← heval]
  have hX : f X = matrixGaussian X * F (X : OnePoint (Mat m n)) := by
    change f X = matrixGaussian X * (f X / matrixGaussian X)
    field_simp [matrixGaussian_ne_zero X]
  have hpoint := (ContinuousMap.norm_coe_le_norm (F - aeval generator p)
    (X : OnePoint (Mat m n))).trans (le_of_lt (by simpa only [dist_eq_norm] using hdist))
  rw [hX, ← mul_sub, norm_mul, mul_comm ε]
  exact mul_le_mul_of_nonneg_left hpoint (norm_nonneg _)

end Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial
