import Langlands.Representation.Whittaker.EntrywiseCharacter
import Mathlib.Algebra.Module.Torsion.Free

/-! # The full functional line and a nonzero spanning form -/

noncomputable section

namespace Langlands.Whittaker

universe uk uV uF

section LinearAlgebra

variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]

/-- Coordinates in a nonzero spanning vector, on the entire submodule. -/
def scalarEquivOfNonzeroSpan (S : Submodule k V) (w : S) (hw : w ≠ 0)
    (hspan : ∀ w' : S, ∃ c : k, w' = c • w) : S ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton k S w)
    ⟨smul_left_injective k hw, fun w' => by
      obtain ⟨c, hc⟩ := hspan w'
      exact ⟨c, hc.symm⟩⟩).symm

/-- A linear equivalence of the whole submodule with the field is exactly
existence of a nonzero element spanning every element of that submodule. -/
theorem nonempty_scalarEquiv_iff (S : Submodule k V) :
    Nonempty (S ≃ₗ[k] k) ↔
      ∃ w : V, w ≠ 0 ∧ w ∈ S ∧ ∀ w', w' ∈ S → ∃ c : k, w' = c • w := by
  constructor
  · rintro ⟨e⟩
    refine ⟨(e.symm 1).val, ?_, (e.symm 1).property, ?_⟩
    · intro hz
      have h : e.symm 1 = 0 := Subtype.ext hz
      have : (1 : k) = 0 := by simpa using congrArg e h
      exact one_ne_zero this
    · intro w' hw'
      refine ⟨e ⟨w', hw'⟩, ?_⟩
      have h : (⟨w', hw'⟩ : S) = e ⟨w', hw'⟩ • e.symm 1 := by
        apply e.injective
        simp
      exact congrArg Subtype.val h
  · rintro ⟨w, hw, hmem, hspan⟩
    refine ⟨scalarEquivOfNonzeroSpan S ⟨w, hmem⟩ ?_ ?_⟩
    · intro hz
      exact hw (congrArg Subtype.val hz)
    · intro w'
      obtain ⟨c, hc⟩ := hspan w'.val w'.property
      exact ⟨c, Subtype.ext hc⟩

end LinearAlgebra

section StandardCharacter

open GeneralLinear HarmonicAnalysis
open scoped BigOperators

variable {F : Type uF} [CommRing F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The full standard functional line is equivalent to the raw double-entry
existence-and-uniqueness condition used by the induced heredity statement. -/
theorem nonempty_standardFunctionalsEquiv_iff
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Nonempty (functionals (upperUnipotent (n + 1) F) (standardCharacter ψ n) ρ ≃ₗ[ℂ] ℂ) ↔
      ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧
        (∀ g : Langlands.GeneralLinear (n + 1) F,
          ((∀ a b, b < a → g.val a b = 0) ∧ ∀ a, g.val a a = 1) →
          ∀ v, ℓ (ρ g v) =
            (∏ a : Fin (n + 1), ∏ b : Fin (n + 1),
              if b.val = a.val + 1 then ψ.complex (g.val a b) else 1) * ℓ v) ∧
        ∀ ℓ',
          (∀ g : Langlands.GeneralLinear (n + 1) F,
            ((∀ a b, b < a → g.val a b = 0) ∧ ∀ a, g.val a a = 1) →
            ∀ v, ℓ' (ρ g v) =
              (∏ a : Fin (n + 1), ∏ b : Fin (n + 1),
                if b.val = a.val + 1 then ψ.complex (g.val a b) else 1) * ℓ' v) →
          ∃ c : ℂ, ℓ' = c • ℓ := by
  rw [← entrywiseCharacter_eq_standardCharacter, nonempty_scalarEquiv_iff]
  simp only [mem_functionals_entrywiseCharacter_iff]

end StandardCharacter
end Langlands.Whittaker
