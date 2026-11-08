import Langlands.Representation.Conductor.JacquetScaledLevel
import Langlands.Representation.Whittaker.DualTransform

/-! # Dual comparison and scaled opposite Jacquet invariance -/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis

universe uF uV

variable {F : Type uF} [Field F] {n : ℕ}

/-- Inverse transpose inverts the diagonal dilation used in the Jacquet group. -/
@[simp] theorem inverseTranspose_jacquetRowDilation (q : Fˣ) :
    inverseTranspose (n + 1) F (jacquetRowDilation n q) =
      (jacquetRowDilation n q)⁻¹ := by
  apply Units.ext
  change (Matrix.diagonal _).transpose = Matrix.diagonal _
  exact Matrix.diagonal_transpose _

/-- Inverse transpose exchanges the integral row and column mirabolics. -/
theorem fieldJacquetMirabolic_map_inverseTranspose (O : Subring F) :
    (fieldJacquetMirabolic O n).map (inverseTranspose (n + 1) F).toMonoidHom =
      integralSubgroup O n ⊓ oppositeMirabolic n F := by
  simpa only [fieldJacquetLevelMirabolic_top, congruenceSubgroup_top] using
    fieldJacquetLevelMirabolic_map_inverseTranspose (n := n) O ⊤

/-- The scaled opposite group transports into the integral row mirabolic. -/
theorem scaledOpposite_inverseTranspose_conjugate_mem (O : Subring F) (q : Fˣ)
    {h : Langlands.GeneralLinear (n + 1) F}
    (hh : h ∈ scaledOppositeJacquetMirabolic O n q) :
    (jacquetRowDilation n q)⁻¹ * inverseTranspose (n + 1) F h *
      jacquetRowDilation n q ∈ fieldJacquetMirabolic O n := by
  change jacquetRowDilation n q * h * (jacquetRowDilation n q)⁻¹ ∈
    integralSubgroup O n ⊓ oppositeMirabolic n F at hh
  rw [← fieldJacquetMirabolic_map_inverseTranspose O] at hh
  obtain ⟨k, hk, he⟩ := hh
  have he' := congrArg (inverseTranspose (n + 1) F) he
  simp only [map_mul, map_inv,
    inverseTranspose_jacquetRowDilation, inv_inv] at he'
  exact he' ▸ hk

section Functions

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- A supplied global comparison of the actual dual function with a right
translate. This definition asserts neither existence nor a contragredient identification. -/
def HasJacquetDualComparison (q : Fˣ)
    (f f' : Langlands.GeneralLinear (n + 1) F → ℂ) (c : ℂ) : Prop :=
  ∀ g, dualFunction n f g = c * f' (g * jacquetRowDilation n q)

/-- Invariance of the actual dual function under inverse transpose gives
invariance of the original function. -/
theorem right_invariant_of_dualFunction
    (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (h : Langlands.GeneralLinear (n + 1) F)
    (hf : ∀ g, dualFunction n f (g * inverseTranspose (n + 1) F h) =
      dualFunction n f g) :
    ∀ g, f (g * h) = f g := by
  have he : rightTranslation ℂ _ h f = f := by
    apply (dualFunction n).injective
    rw [dualFunction_translate]
    exact funext hf
  exact fun g => congrFun he g

/-- A global dual comparison with an integral-Jacquet-invariant function gives
the scaled opposite invariance of the original function. -/
theorem right_scaledOpposite_invariant_of_dual_comparison
    (O : Subring F) (q : Fˣ)
    (f f' : Langlands.GeneralLinear (n + 1) F → ℂ) (c : ℂ)
    (hD : HasJacquetDualComparison q f f' c)
    (hP' : ∀ k ∈ fieldJacquetMirabolic O n, ∀ g, f' (g * k) = f' g) :
    ∀ h ∈ scaledOppositeJacquetMirabolic O n q, ∀ g, f (g * h) = f g := by
  intro h hh
  apply right_invariant_of_dualFunction f h
  intro g
  let d := jacquetRowDilation n q
  let k := d⁻¹ * inverseTranspose (n + 1) F h * d
  have hk : k ∈ fieldJacquetMirabolic O n :=
    scaledOpposite_inverseTranspose_conjugate_mem O q hh
  have he : (g * inverseTranspose (n + 1) F h) * d = (g * d) * k := by
    dsimp only [k]
    simp only [mul_assoc, mul_inv_cancel_left]
  change dualFunction n f (g * inverseTranspose (n + 1) F h) = dualFunction n f g
  rw [hD, hD]
  change c * f' ((g * inverseTranspose (n + 1) F h) * d) = c * f' (g * d)
  rw [he, hP' k hk]

/-- At a natural uniformizer scale, the two integral invariances and the dual
comparison give the actual level-fixed coefficient-model vector. -/
theorem mem_levelFixedVectors_of_dual_comparison [ValuativeRel F]
    (hn : 0 < n) (ϖ : Fˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (a : ℕ)
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n π) (w : (coefficientModel π ℓ).toSubmodule)
    (f' : Langlands.GeneralLinear (n + 1) F → ℂ) (c : ℂ)
    (hD : HasJacquetDualComparison (ϖ ^ (-(a : ℤ))) w.val.val f' c)
    (hP : w ∈ fixedVectors (modelRepresentation π ℓ)
      (fieldJacquetMirabolic (ValuativeRel.valuation F).integer n))
    (hP' : ∀ k ∈ fieldJacquetMirabolic (ValuativeRel.valuation F).integer n,
      ∀ g, f' (g * k) = f' g) :
    w ∈ levelFixedVectors (modelRepresentation π ℓ) a := by
  apply mem_levelFixedVectors_of_scaled_jacquet_invariant
    (modelRepresentation π ℓ) hn ϖ hϖ a w hP
  intro h
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact right_scaledOpposite_invariant_of_dual_comparison _ _ w.val.val f' c
    hD hP' h.val h.property g

/-- For a nonzero Whittaker function, the supplied dual comparison also forces
a nonnegative integer scale and invariance at its natural-number level. -/
theorem right_level_toNat_invariant_of_dual_comparison [ValuativeRel F]
    [ValuativeRel.IsRankLeOne F] (ψ : UnitaryAdditiveCharacter F) (hn : 0 < n)
    (ϖ : Fˣ) (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)
    (m : ℤ)
    (W : (equivariantFunctions (upperUnipotent (n + 1) F)
      (standardCharacter ψ n)).toSubmodule) (hW : W ≠ 0)
    (f' : Langlands.GeneralLinear (n + 1) F → ℂ) (c : ℂ)
    (hD : HasJacquetDualComparison (ϖ ^ (-m)) W.val f' c)
    (hP : ∀ h ∈ fieldJacquetMirabolic (ValuativeRel.valuation F).integer n,
      ∀ g, W.val (g * h) = W.val g)
    (hP' : ∀ k ∈ fieldJacquetMirabolic (ValuativeRel.valuation F).integer n,
      ∀ g, f' (g * k) = f' g) :
    0 ≤ m ∧ ∀ h ∈ levelSubgroup F n m.toNat, ∀ g, W.val (g * h) = W.val g :=
  right_level_toNat_invariant_of_uniformizer_jacquet_invariant ψ hn ϖ hϖ m W hW hP
    (right_scaledOpposite_invariant_of_dual_comparison _ _ W.val f' c hD hP')

end Functions

end Langlands.Conductor
