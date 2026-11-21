import Langlands.HarmonicAnalysis.ArchimedeanCharacterParameters
import Langlands.Representation.Archimedean.MatrixTraceTestCasimir
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The real infinitesimal parameters of the upper-root characters -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Langlands.HarmonicAnalysis Langlands.GeneralLinear

namespace Langlands.Archimedean

universe uF

variable {F : Type uF} [RCLike F]

/-- The real and imaginary frequencies give the phase of an actual
nontrivial unitary additive character and a nonzero trace-dual coefficient. -/
theorem exists_whittakerRootPhase (ψ : UnitaryAdditiveCharacter F) :
    ∃ a b : ℝ, (∀ z : F, ψ z = Circle.exp (a * RCLike.re z + b * RCLike.im z)) ∧
      a • (1 : F) - b • (RCLike.I : F) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_circle_exp_mul_of_continuous_add
    (fun t : ℝ => ψ (t : F)) (ψ.continuous_toFun.comp RCLike.continuous_ofReal)
    (by simp)
    (fun x y => by
      rw [RCLike.ofReal_add]
      exact ψ.toAddChar.map_add_eq_mul _ _)
  obtain ⟨b, hb⟩ := exists_circle_exp_mul_of_continuous_add
    (fun t : ℝ => ψ ((t : F) * RCLike.I))
    (ψ.continuous_toFun.comp (RCLike.continuous_ofReal.mul_const _))
    (by simp)
    (fun x y => by
      rw [RCLike.ofReal_add, add_mul]
      exact ψ.toAddChar.map_add_eq_mul _ _)
  have hphase (z : F) : ψ z = Circle.exp (a * RCLike.re z + b * RCLike.im z) := by
    conv_lhs => rw [← RCLike.re_add_im z]
    rw [ψ.toAddChar.map_add_eq_mul]
    exact (congrArg₂ (· * ·) (ha _) (hb _)).trans (Circle.exp_add _ _).symm
  refine ⟨a, b, hphase, fun h => ψ.nontrivial ?_⟩
  have ha₀ : a = 0 := by
    have hz := congrArg (RCLike.re : F → ℝ) h
    simpa [RCLike.smul_re] using hz
  have hb₀ : b • (RCLike.I : F) = 0 := by simpa [ha₀] using h
  have hbi (z : F) : b * RCLike.im z = 0 := by
    rcases smul_eq_zero.mp hb₀ with hb₀ | hI
    · rw [hb₀, zero_mul]
    · have hi := RCLike.I_mul_re z
      rw [hI, zero_mul, map_zero] at hi
      rw [neg_eq_zero.mp hi.symm, mul_zero]
  apply DFunLike.ext
  intro z
  change ψ z = 1
  rw [hphase, ha₀, zero_mul, zero_add, hbi, Circle.exp_zero]

/-- On a real line in the scalar field, the derivative of the
unitary character at zero is purely imaginary. -/
theorem hasDerivAt_whittakerRootPhase (ψ : UnitaryAdditiveCharacter F) (a b : ℝ)
    (hψ : ∀ z : F, ψ z = Circle.exp (a * RCLike.re z + b * RCLike.im z)) (s : F) :
    HasDerivAt (fun t : ℝ => ψ.complex (t • s))
      ((a * RCLike.re s + b * RCLike.im s : ℝ) * Complex.I) 0 := by
  let c := a * RCLike.re s + b * RCLike.im s
  have he : (fun t : ℝ => ψ.complex (t • s)) =
      fun t : ℝ => Complex.exp (((t : ℂ) * (c : ℂ)) * Complex.I) := by
    funext t
    rw [ψ.complex_apply, hψ, Circle.coe_exp]
    congr 1
    simp only [RCLike.smul_re, RCLike.smul_im, c, Complex.ofReal_add, Complex.ofReal_mul]
    ring
  rw [he]
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 :=
    Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, c]
    using ((hc.mul_const (c : ℂ)).mul_const Complex.I).cexp

/-- The elementary transvection in one actual positive upper root. -/
def upperRootTransvection {n : ℕ} (p : MatrixPositiveRoot n) (z : F) :
    upperUnipotent n F := by
  refine ⟨Matrix.GeneralLinearGroup.transvection p.val.1 p.val.2 (ne_of_lt p.property) z, ?_⟩
  constructor
  · intro i j hij
    change j < i at hij
    have h : ¬ (p.val.1 = i ∧ p.val.2 = j) := by
      rintro ⟨rfl, rfl⟩
      exact (not_lt_of_gt p.property) hij
    change Matrix.transvection p.val.1 p.val.2 z i j = 0
    simp [Matrix.transvection, Matrix.single, h, Matrix.one_apply_ne (ne_of_gt hij)]
  · intro i
    have h : ¬ (p.val.1 = i ∧ p.val.2 = i) := by
      rintro ⟨h₁, h₂⟩
      exact (ne_of_lt p.property) (h₁.trans h₂.symm)
    change Matrix.transvection p.val.1 p.val.2 z i i = 1
    simp [Matrix.transvection, Matrix.single, h]

@[simp]
theorem upperRootTransvection_val {n : ℕ} (p : MatrixPositiveRoot n) (z : F) :
    (upperRootTransvection p z).val.val =
      1 + Matrix.single p.val.1 p.val.2 z := rfl

/-- The upper-root character evaluates to the given additive character
on simple roots and is trivial on every other positive root. -/
theorem standardCharacter_upperRootTransvection (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    (p : MatrixPositiveRoot (r + 1)) (z : F) :
    (Langlands.Whittaker.standardCharacter ψ r (upperRootTransvection p z) : ℂ) =
      if ∃ i : Fin r, i.castSucc = p.val.1 ∧ i.succ = p.val.2 then ψ.complex z else 1 := by
  rw [Langlands.Whittaker.standardCharacter_apply]
  have hslot (i : Fin r) :
      (upperRootTransvection p z).val i.castSucc i.succ =
        if i.castSucc = p.val.1 ∧ i.succ = p.val.2 then z else 0 := by
    rw [upperRootTransvection_val]
    have hi : i.castSucc ≠ i.succ := by
      intro h
      have he := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at he
      omega
    simp [Matrix.single, hi, eq_comm]
  simp_rw [hslot]
  split_ifs with h
  · obtain ⟨k, hk, hk'⟩ := h
    rw [Finset.sum_eq_single k]
    · simp [hk, hk']
    · intro i _ hi
      have he : i.castSucc ≠ p.val.1 := fun he => hi (Fin.castSucc_injective _ (he.trans hk.symm))
      simp [he]
    · simp
  · rw [Finset.sum_eq_zero]
    · exact ψ.complex.map_zero_eq_one
    · intro i _
      simp [show ¬ (i.castSucc = p.val.1 ∧ i.succ = p.val.2) from fun hi => h ⟨i, hi⟩]

/-- The differential of the standard character on an actual upper-root line. -/
theorem hasDerivAt_standardCharacter_upperRootTransvection
    (ψ : UnitaryAdditiveCharacter F) (a b : ℝ)
    (hψ : ∀ z : F, ψ z = Circle.exp (a * RCLike.re z + b * RCLike.im z))
    {r : ℕ} (p : MatrixPositiveRoot (r + 1)) (s : F) :
    HasDerivAt
      (fun t : ℝ => (Langlands.Whittaker.standardCharacter ψ r (upperRootTransvection p (t • s)) : ℂ))
      ((↑(if ∃ i : Fin r, i.castSucc = p.val.1 ∧ i.succ = p.val.2
          then a * RCLike.re s + b * RCLike.im s else 0) : ℂ) * Complex.I) 0 := by
  simp_rw [standardCharacter_upperRootTransvection]
  split_ifs
  · exact hasDerivAt_whittakerRootPhase ψ a b hψ s
  · simpa only [Complex.ofReal_zero, zero_mul] using (hasDerivAt_const (0 : ℝ) (1 : ℂ))

end Langlands.Archimedean
