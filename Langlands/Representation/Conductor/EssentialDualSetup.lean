import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.Conductor.EssentialStatement
import Langlands.Representation.RankinSelberg.DualWhittakerType
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Conductor.JacquetDualInvariance

/-!
# Setup for the dual essential vector

The inverse-transpose pullback of a generic representation is generic for
`ψ.scale (-1)`, the dual functional recast for `ψ.scale (-1)` is nonzero, and
Jacquet's normalizations persist when `ψ` is replaced by `ψ.scale (-1)`.
A dual comparison in the form of JPSS (5.3), with the translate
`diag(ϖ^m, ..., ϖ^m, 1)`, is a Jacquet dual comparison for a central translate.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory

universe uF uV

section Dual

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] (ψ : UnitaryAdditiveCharacter F)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The dual functional of `ℓ`, viewed as a standard functional for `ψ.scale (-1)`. -/
def scaledDualFunctional (ℓ : glFunctionals ψ n π) :
    glFunctionals (ψ.scale (-1)) n (inverseTransposePullback π) :=
  firstDualFunctional ψ π ℓ

@[simp] theorem scaledDualFunctional_val (ℓ : glFunctionals ψ n π) :
    (scaledDualFunctional ψ π ℓ).val = (dualFunctional ψ π ℓ).val := rfl

theorem scaledDualFunctional_ne_zero (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) :
    (scaledDualFunctional ψ π ℓ).val ≠ 0 :=
  firstDualFunctional_ne_zero ψ π hℓ

/-- The inverse-transpose pullback of a `ψ`-generic representation is
`ψ.scale (-1)`-generic. -/
theorem isGeneric_inverseTransposePullback (hπ : IsGeneric ψ n π) :
    IsGeneric (ψ.scale (-1)) n (inverseTransposePullback π) := by
  obtain ⟨hirr, hadm, ℓ, hℓ⟩ := hπ
  refine ⟨(isIrreducible_comp_continuousMulEquiv_iff π
      (inverseTransposeContinuous (n + 1) F)).2 hirr,
    isAdmissible_comp_continuousMulEquiv π (inverseTransposeContinuous (n + 1) F) hadm,
    scaledDualFunctional ψ π ℓ, scaledDualFunctional_ne_zero ψ π ℓ hℓ⟩

end Dual

section Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Conductor `O` is preserved by `x ↦ ψ(-x)`. -/
theorem hasIntegerConductor_scale_neg_one {ψ : UnitaryAdditiveCharacter F}
    (hψ : HasIntegerConductor ψ) : HasIntegerConductor (ψ.scale (-1)) := by
  obtain ⟨h1, h2⟩ := hψ
  refine ⟨fun x hx => ?_, fun x hx => h2 x fun y hy => ?_⟩
  · rw [UnitaryAdditiveCharacter.scale_apply]
    exact h1 _ (by simpa using neg_mem hx)
  · have := hx (-y) (neg_mem hy)
    rw [UnitaryAdditiveCharacter.scale_apply] at this
    simpa using this

variable {n : ℕ} [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}

/-- Jacquet's normalizations for `ψ` give those for `ψ.scale (-1)`, with the
same residue cardinality, absolute value, uniformizer and quotient measure. -/
theorem IsJacquetNormalization.scaleNegOne (h : IsJacquetNormalization q ψ abv ϖ μ) :
    IsJacquetNormalization q (ψ.scale (-1)) abv ϖ μ :=
  { h with conductor := hasIntegerConductor_scale_neg_one h.conductor }

end Normalization

section Translate

variable {F : Type uF} [Field F] {n : ℕ}

/-- `diag(a, ..., a, 1)` is the scalar `a` times `diag(1, ..., 1, a⁻¹)`. -/
theorem rankInclusion_scalar_eq (a : Fˣ) :
    rankInclusion 1 (scalar (n := n + 1) a) =
      jacquetRowDilation (n + 1) a⁻¹ * scalar a := by
  apply Units.ext
  ext i j
  change (blockSum (scalar (n := n + 1) a, (1 : Langlands.GeneralLinear 1 F))).val i j =
    ((jacquetRowDilation (n + 1) a⁻¹).val * (scalar (n := (n + 1) + 1) a).val) i j
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hd : (jacquetRowDilation (n + 1) a⁻¹).val = Matrix.diagonal (fun i : Fin ((n + 1) + 1) =>
      if i = Fin.last (n + 1) then ((a⁻¹ : Fˣ) : F) else 1) := rfl
  rw [hd, Matrix.diagonal_mul_diagonal]
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [show (blockSum (scalar (n := n + 1) a, (1 : Langlands.GeneralLinear 1 F))).val
        (Fin.last (n + 1)) (Fin.last (n + 1)) = 1 by
      exact (blockSum_apply_right (scalar (n := n + 1) a)
        (1 : Langlands.GeneralLinear 1 F) (0 : Fin 1) (0 : Fin 1)).trans (by rfl)]
    simp
  · rw [show (blockSum (scalar (n := n + 1) a, (1 : Langlands.GeneralLinear 1 F))).val
        (Fin.last (n + 1)) j.castSucc = 0 from
      blockSum_apply_right_left _ _ (0 : Fin 1) j]
    simp [(Fin.castSucc_ne_last j).symm]
  · rw [show (blockSum (scalar (n := n + 1) a, (1 : Langlands.GeneralLinear 1 F))).val
        i.castSucc (Fin.last (n + 1)) = 0 from
      blockSum_apply_left_right _ _ i (0 : Fin 1)]
    simp [Fin.castSucc_ne_last i]
  · rw [show (blockSum (scalar (n := n + 1) a, (1 : Langlands.GeneralLinear 1 F))).val
        i.castSucc j.castSucc = (scalar (n := n + 1) a).val i j from
      blockSum_apply_left _ _ i j]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Fin.castSucc_ne_last]

/-- Right invariance under a subgroup passes to a central translate. -/
theorem right_invariant_central_translate (a : Fˣ)
    (H : Subgroup (Langlands.GeneralLinear ((n + 1) + 1) F))
    (f' : Langlands.GeneralLinear ((n + 1) + 1) F → ℂ)
    (hf' : ∀ k ∈ H, ∀ g, f' (g * k) = f' g) :
    ∀ k ∈ H, ∀ g, f' (g * k * scalar (n := (n + 1) + 1) a) =
      f' (g * scalar (n := (n + 1) + 1) a) := by
  intro k hk g
  rw [mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute a k, ← mul_assoc,
    hf' k hk]

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- A dual comparison with the translate `diag(ϖ^m, ..., ϖ^m, 1)` is a Jacquet dual
comparison at scale `ϖ^(-m)` for the translate of `f'` by the central scalar `ϖ^m`. -/
theorem hasJacquetDualComparison_of_rankInclusion_scalar (ϖ : Fˣ) (m : ℤ)
    (f f' : Langlands.GeneralLinear ((n + 1) + 1) F → ℂ) (C : ℂ)
    (h : ∀ g, dualFunction (n + 1) f g =
      C * f' (g * rankInclusion 1 (scalar (n := n + 1) (ϖ ^ m)))) :
    HasJacquetDualComparison (ϖ ^ (-m)) f
      (fun g => f' (g * scalar (n := (n + 1) + 1) (ϖ ^ m))) C := by
  intro g
  rw [h, rankInclusion_scalar_eq, zpow_neg, ← mul_assoc]

/-- JPSS (5.3) in its source form, together with the integral row-mirabolic
invariance of both functions, puts `w` in the level-`m` fixed space. -/
theorem mem_levelFixedVectors_of_rankInclusion_dual_comparison [ValuativeRel F]
    (ϖ : Fˣ) (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (m : ℕ)
    (ψ : UnitaryAdditiveCharacter F) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
    (ℓ : glFunctionals ψ (n + 1) π) (w : (coefficientModel π ℓ).toSubmodule)
    (f' : Langlands.GeneralLinear ((n + 1) + 1) F → ℂ) (C : ℂ)
    (h : ∀ g, dualFunction (n + 1) w.val.val g =
      C * f' (g * rankInclusion 1 (scalar (n := n + 1) (ϖ ^ (m : ℤ)))))
    (hP : w ∈ fixedVectors (modelRepresentation π ℓ)
      (fieldJacquetMirabolic (ValuativeRel.valuation F).integer (n + 1)))
    (hP' : ∀ k ∈ fieldJacquetMirabolic (ValuativeRel.valuation F).integer (n + 1),
      ∀ g, f' (g * k) = f' g) :
    w ∈ levelFixedVectors (modelRepresentation π ℓ) m :=
  mem_levelFixedVectors_of_dual_comparison (Nat.succ_pos n) ϖ hϖ m ψ π ℓ w _ C
    (hasJacquetDualComparison_of_rankInclusion_scalar ϖ m w.val.val f' C h) hP
    (right_invariant_central_translate _ _ f' hP')

end Translate

end Langlands.Conductor
