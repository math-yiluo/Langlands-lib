import Langlands.Representation.Archimedean.GKModule

/-!
# Reduction of the complex generic standard-parameter statement

`ComplexGenericStandardParameterStatement` says that every irreducible admissible generic
`(𝔤𝔩_n(ℂ), U(n))`-module has the standard-module parameter of some list of complex
characters. This file splits it into two statements:

* `ComplexLanglandsQuotientStatement` (Langlands classification, Knapp 1994, Theorem 4): every
  irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module receives a nonzero `(𝔤, K)`-intertwining
  map from the `U(n)`-finite functions of the principal series of `n` characters whose
  exponents have non-increasing real parts;
* `ComplexGenericStandardInjectiveStatement` (Vogan 1978, Kostant 1978, Matumoto 1987): for
  such characters, every surjective intertwining map onto an irreducible admissible generic
  module is injective.

`complexGenericParameterReduction` proves that the two imply the target. On the way,
`surjective_of_isComplexStandardIntertwining` shows that a nonzero intertwining map into an
irreducible module is surjective.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

universe uV

/-- The Langlands order on a list of complex characters `zᵢ ↦ (zᵢ/‖zᵢ‖)^{lᵢ} ‖zᵢ‖^{2 tᵢ}`:
the real parts of the exponents do not increase, `Re t₁ ≥ Re t₂ ≥ ⋯` (Knapp 1994, (4.3)). -/
def IsComplexLanglandsOrdered (ds : List ComplexCharacterData) : Prop :=
  ds.Pairwise fun d e => e.exponent.re ≤ d.exponent.re

section Intertwining

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `A` is a `(𝔤, K)`-intertwining map from the `U(n)`-finite functions of the standard module
of `ds` to `(ρ, π)`: the right translate by `k ∈ U(n)` and the right derivative along a real
direction `X ∈ 𝔤𝔩_n(ℂ)` of a `U(n)`-finite function are again `U(n)`-finite functions of the
standard module, and `A` carries them to `ρ(k)` and `π(1 ⊗ X)` of its value. These are the
two equivariance clauses of `HasComplexStandardParameter`. -/
def IsComplexStandardIntertwining (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ds : List ComplexCharacterData)
    (A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V) : Prop :=
  (∀ (k : unitaryCompact ℂ n)
      (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
    ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
        (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
          kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
      A ⟨_, hf⟩ =
        ρ ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (A f)) ∧
  ∀ (X : Matrix (Fin n) (Fin n) ℂ)
      (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
    ∃ hf : rightDerivative (matrixModel ℂ n) X (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
        kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
      A ⟨_, hf⟩ = π (1 ⊗ₜ X) (A f)

/-- `HasComplexStandardParameter` is the rank condition together with an injective
intertwining map. -/
theorem hasComplexStandardParameter_iff
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ds : List ComplexCharacterData) :
    HasComplexStandardParameter n ρ π ds ↔
      ds.length = n ∧
        ∃ A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V,
          Function.Injective A ∧ IsComplexStandardIntertwining n ρ π ds A :=
  Iff.rfl

/-- A nonzero intertwining map into an irreducible module is surjective: its range is stable
under `ρ` and under `π`, since `π` is complex linear and the elements `1 ⊗ X` span
`ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)` over `ℂ`. -/
theorem surjective_of_isComplexStandardIntertwining
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
    {ds : List ComplexCharacterData}
    {A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V}
    (hirr : IsIrreducibleGKModule ρ π) (hA : IsComplexStandardIntertwining n ρ π ds A)
    (h0 : A ≠ 0) : Function.Surjective A := by
  have hW : LinearMap.range A = ⊥ ∨ LinearMap.range A = ⊤ := by
    apply hirr.2
    · rintro k w ⟨f, rfl⟩
      obtain ⟨hf, h⟩ := hA.1 ⟨Unitary.toUnits k, k.2⟩ f
      exact ⟨_, h⟩
    · rintro Y w ⟨f, rfl⟩
      induction Y using TensorProduct.inductionOn with
      | tmul z X =>
        obtain ⟨hf, h⟩ := hA.2 X f
        have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hz, map_smul, LinearMap.smul_apply, ← h]
        exact Submodule.smul_mem _ _ ⟨_, rfl⟩
      | add Y₁ Y₂ h₁ h₂ =>
        rw [map_add, LinearMap.add_apply]
        exact add_mem h₁ h₂
  rcases hW with h | h
  · exact absurd (LinearMap.range_eq_bot.mp h) h0
  · exact LinearMap.range_eq_top.mp h

end Intertwining

/-- Langlands classification of irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-modules in the form
needed here (Knapp 1994, Theorem 4): every irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module
`(ρ, π)` receives a nonzero intertwining map from the `U(n)`-finite functions of the standard
module of some list of `n` complex characters in the Langlands order. -/
def ComplexLanglandsQuotientStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ ds : List ComplexCharacterData, ds.length = n ∧ IsComplexLanglandsOrdered ds ∧
        ∃ A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V,
          A ≠ 0 ∧ IsComplexStandardIntertwining n ρ π ds A

/-- Irreducibility of the standard module of a generic Langlands quotient, in the form needed
here (Vogan 1978; Kostant 1978; Matumoto 1987): for `n` complex characters `ds` in the
Langlands order, every surjective intertwining map from the `U(n)`-finite functions of their
standard module onto an irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module is
injective. -/
def ComplexGenericStandardInjectiveStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ds : List ComplexCharacterData)
    (A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsComplexGenericGKModule n π → ds.length = n → IsComplexLanglandsOrdered ds →
        Function.Surjective A → IsComplexStandardIntertwining n ρ π ds A →
          Function.Injective A

/-- The two statements above imply `ComplexGenericStandardParameterStatement`. -/
def ComplexGenericParameterReductionStatement : Prop :=
  ComplexLanglandsQuotientStatement.{uV} → ComplexGenericStandardInjectiveStatement.{uV} →
    ComplexGenericStandardParameterStatement.{uV}

/-- Proof of the reduction: the Langlands quotient map is nonzero, hence surjective onto the
irreducible module, hence injective for a generic module. -/
theorem complexGenericParameterReduction : ComplexGenericParameterReductionStatement.{uV} := by
  intro h₁ h₂ n V _ _ ρ π hgk hirr hadm hgen
  obtain ⟨ds, hlen, hord, A, h0, hA⟩ := h₁ n V ρ π hgk hirr hadm
  have hsurj := surjective_of_isComplexStandardIntertwining n hirr hA h0
  exact ⟨ds, hlen, A, h₂ n V ρ π ds A hgk hirr hadm hgen hlen hord hsurj hA, hA⟩

end Langlands.Archimedean
