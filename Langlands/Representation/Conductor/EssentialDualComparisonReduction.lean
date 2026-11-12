import Langlands.Representation.RankinSelberg.HighlyRamified.LowerRowDual
import Langlands.Representation.Conductor.EssentialDualSetup
import Langlands.Representation.Conductor.EssentialUniquenessReduction
import Langlands.Representation.Conductor.SphericalTranslation
import Langlands.Representation.RankinSelberg.HighlyRamified.UnitarySeparation

/-!
# Algebraic reduction for the dual comparison of essential vectors

These internal lemmas reduce comparison on the full group to proportional
spherical integrals, using mirabolic restriction injectivity as a separate input.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory

universe uF uV

section Algebra

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
variable {ψ : UnitaryAdditiveCharacter F} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (ℓ : glFunctionals ψ (n + 1) π)

/-- Mirabolic injectivity promotes right integral Levi invariance from the
Levi slice to every point of the full group. -/
theorem right_integral_levi_invariant_of_restriction [ValuativeRel F]
    (hinj : IsMirabolicRestrictionInjective π ℓ)
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (k : integralSubgroup (ValuativeRel.valuation F).integer n)
    (g : Langlands.GeneralLinear ((n + 1) + 1) F) :
    w.val.val (g * rankInclusion 1 k.val) = w.val.val g := by
  have he : modelRepresentation π ℓ (rankInclusion 1 k.val) w = w := by
    apply modelMirabolicRestriction_injective_of_carrier ψ π ℓ hinj
    funext p
    exact whittaker_mirabolic_eq_of_levi_eq ψ
      (modelRepresentation π ℓ (rankInclusion 1 k.val) w).val w.val
      (fun a => by
        change w.val.val (rankInclusion 1 a * rankInclusion 1 k.val) = _
        rw [← map_mul]
        exact hw a k) p
  exact congrArg (fun z : (coefficientModel π ℓ).toSubmodule => z.val.val g) he

omit [TopologicalSpace F] in
private theorem inverseTranspose_mem_integralSubgroup (O : Subring F)
    (k : Langlands.GeneralLinear (n + 1) F) (hk : k ∈ integralSubgroup O n) :
    inverseTranspose (n + 1) F k ∈ integralSubgroup O n := by
  obtain ⟨h₁, h₂⟩ := (mem_integralSubgroup O n k).mp hk
  exact (mem_integralSubgroup O n _).mpr
    ⟨fun i j => h₂ j i, fun i j => by
      rw [← map_inv, inverseTranspose_entry, inv_inv]
      exact h₁ j i⟩

variable [IsTopologicalRing F]

/-- Place the actual dual function in the model for any functional with the
prescribed dual-functional value. -/
def dualComparisonModelMap
    (ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π))
    (hℓ' : ℓ'.val = (dualFunctional ψ π ℓ).val) :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel (inverseTransposePullback π) ℓ').toSubmodule := by
  have he : ℓ' = firstDualFunctional ψ π ℓ := Subtype.ext hℓ'
  subst ℓ'
  exact firstDualModelMap ψ π ℓ

@[simp] theorem dualComparisonModelMap_apply
    (ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π))
    (hℓ' : ℓ'.val = (dualFunctional ψ π ℓ).val)
    (w : (coefficientModel π ℓ).toSubmodule)
    (g : Langlands.GeneralLinear ((n + 1) + 1) F) :
    (dualComparisonModelMap π ℓ ℓ' hℓ' w).val.val g =
      dualFunction (n + 1) w.val.val g := by
  have he : ℓ' = firstDualFunctional ψ π ℓ := Subtype.ext hℓ'
  subst ℓ'
  rfl

/-- The dual of a restriction-invariant vector is restriction-invariant,
provided restriction in the original model is injective. -/
theorem dualComparisonModelMap_integralInvariant [ValuativeRel F]
    (hinj : IsMirabolicRestrictionInjective π ℓ)
    (ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π))
    (hℓ' : ℓ'.val = (dualFunctional ψ π ℓ).val)
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : IsIntegralInvariantOnRestriction π ℓ w) :
    IsIntegralInvariantOnRestriction (inverseTransposePullback π) ℓ'
      (dualComparisonModelMap π ℓ ℓ' hℓ' w) := by
  intro g k
  simp only [dualComparisonModelMap_apply, dualFunction_apply, map_mul,
    Langlands.RankinSelberg.HighlyRamified.inverseTranspose_rankInclusion]
  rw [← mul_assoc]
  exact right_integral_levi_invariant_of_restriction π ℓ hinj w hw
    ⟨inverseTranspose (n + 1) F k.val,
      inverseTranspose_mem_integralSubgroup _ k.val k.property⟩ _

omit [IsTopologicalRing F] in
/-- Translating on the right by a scalar in the corank-one Levi preserves
integral invariance of the restriction. -/
theorem integralInvariant_rankInclusion_scalar_translate [ValuativeRel F]
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : IsIntegralInvariantOnRestriction π ℓ w) (a : Fˣ) :
    IsIntegralInvariantOnRestriction π ℓ
      (modelRepresentation π ℓ (rankInclusion 1 (scalar (n := n + 1) a)) w) := by
  intro g k
  change w.val.val (rankInclusion 1 (g * k.val) *
      rankInclusion 1 (scalar a)) =
    w.val.val (rankInclusion 1 g * rankInclusion 1 (scalar a))
  rw [← map_mul, ← map_mul, mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute,
    ← mul_assoc]
  exact hw (g * scalar a) k

end Algebra

section Separation

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (ℓ : glFunctionals ψ (n + 1) π)

/-- Proportional spherical integrals at unitary parameters determine
restriction-invariant smooth model vectors, assuming mirabolic injectivity. -/
theorem eq_smul_of_unit_spherical_integrals (hπ : IsSmooth π)
    (hinj : IsMirabolicRestrictionInjective π ℓ)
    (u v : (coefficientModel π ℓ).toSubmodule)
    (hu : IsIntegralInvariantOnRestriction π ℓ u)
    (hv : IsIntegralInvariantOnRestriction π ℓ v) (C : ℂ)
    (hint : ∀ x : Fin (n + 1) → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) →
      ∃ a : ℝ, ∀ s : ℝ, a < s →
        CorankOneConverges ψ abv μ u.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s ∧
        CorankOneConverges ψ abv μ v.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s ∧
        corankOneIntegral ψ abv μ u.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s =
          C * corankOneIntegral ψ abv μ v.val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) :
    u = C • v := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mirabolic_eq_zero π ℓ hinj
  apply HighlyRamified.eq_zero_on_mirabolic_of_unit_integrals_eq_zero h π hπ ℓ
    (u - C • v)
  · intro g k
    change u.val.val (rankInclusion 1 (g * k.val)) -
        C * v.val.val (rankInclusion 1 (g * k.val)) =
      u.val.val (rankInclusion 1 g) - C * v.val.val (rankInclusion 1 g)
    rw [hu g k, hv g k]
  · intro x hx
    obtain ⟨a, ha⟩ := hint x hx
    refine ⟨a, fun s hs => ?_⟩
    obtain ⟨hcu, hcv, he⟩ := ha s hs
    change CorankOneConverges ψ abv μ (u.val - C • v.val) _ s ∧
      corankOneIntegral ψ abv μ (u.val - C • v.val) _ s = 0
    have hcv' := Conductor.CorankOneConverges.smul ψ abv μ hcv C
    refine ⟨Conductor.CorankOneConverges.sub ψ abv μ hcu hcv', ?_⟩
    rw [Conductor.corankOneIntegral_sub ψ abv μ hcu hcv',
      Conductor.corankOneIntegral_smul, he, sub_self]

end Separation

section DualComparison

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h' : IsJacquetNormalization q (ψ.scale (-1)) abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (ℓ : glFunctionals ψ (n + 1) π)

/-- The analytic comparison of unitary spherical integrals implies the
pointwise dual comparison, assuming mirabolic injectivity in both models.
This is a conditional reduction; it supplies no functional equation. -/
theorem dualComparison_of_unit_spherical_integrals (hπ : IsSmooth π)
    (hinj : IsMirabolicRestrictionInjective π ℓ)
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π))
    (hℓ' : ℓ'.val = (dualFunctional ψ π ℓ).val)
    (hinj' : IsMirabolicRestrictionInjective (inverseTransposePullback π) ℓ')
    (w' : (coefficientModel (inverseTransposePullback π) ℓ').toSubmodule)
    (hw' : IsIntegralInvariantOnRestriction (inverseTransposePullback π) ℓ' w')
    (m : ℤ)
    (hint : ∃ C : ℂ, ∀ x : Fin (n + 1) → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) →
      ∃ a : ℝ, ∀ s : ℝ, a < s →
        CorankOneConverges (ψ.scale (-1)) abv μ
          (dualComparisonModelMap π ℓ ℓ' hℓ' w).val
          (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x) s ∧
        CorankOneConverges (ψ.scale (-1)) abv μ
          (modelRepresentation (inverseTransposePullback π) ℓ'
            (rankInclusion 1 (scalar (ϖ ^ m))) w').val
          (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x) s ∧
        corankOneIntegral (ψ.scale (-1)) abv μ
          (dualComparisonModelMap π ℓ ℓ' hℓ' w).val
          (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x) s =
          C * corankOneIntegral (ψ.scale (-1)) abv μ
            (modelRepresentation (inverseTransposePullback π) ℓ'
              (rankInclusion 1 (scalar (ϖ ^ m))) w').val
            (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x) s) :
    ∃ C : ℂ, ∀ g : Langlands.GeneralLinear ((n + 1) + 1) F,
      dualFunction (n + 1) w.val.val g =
        C * w'.val.val (g * rankInclusion 1 (scalar (ϖ ^ m))) := by
  obtain ⟨C, hC⟩ := hint
  have he := eq_smul_of_unit_spherical_integrals h' (inverseTransposePullback π) ℓ'
    (inverseTransposePullback_isSmooth π hπ) hinj'
    (dualComparisonModelMap π ℓ ℓ' hℓ' w)
    (modelRepresentation (inverseTransposePullback π) ℓ'
      (rankInclusion 1 (scalar (ϖ ^ m))) w')
    (dualComparisonModelMap_integralInvariant π ℓ hinj ℓ' hℓ' w hw)
    (integralInvariant_rankInclusion_scalar_translate (inverseTransposePullback π) ℓ'
      w' hw' (ϖ ^ m)) C hC
  refine ⟨C, fun g => ?_⟩
  have hf := congrArg
    (fun z : (coefficientModel (inverseTransposePullback π) ℓ').toSubmodule =>
      z.val.val g) he
  change (dualComparisonModelMap π ℓ ℓ' hℓ' w).val.val g =
    C * w'.val.val (g * rankInclusion 1 (scalar (ϖ ^ m))) at hf
  simpa only [dualComparisonModelMap_apply] using hf

end DualComparison

end Langlands.Conductor
