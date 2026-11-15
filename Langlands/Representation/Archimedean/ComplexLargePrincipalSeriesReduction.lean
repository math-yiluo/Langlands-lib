import Langlands.Representation.Archimedean.ComplexGenericStandardInjectiveReduction

/-!
# Reduction of Vogan's theorem for large `(𝔤𝔩_n(ℂ), U(n))`-modules

`ComplexLargePrincipalSeriesStatement` (V1; Vogan 1978, Theorem 6.2 (a) ⇒ (f)) says that every
irreducible admissible large `(𝔤𝔩_n(ℂ), U(n))`-module has the standard-module parameter of some
list of `n` complex characters. Vogan's proof first writes the module as a Langlands quotient
and then shows that the standard module is irreducible. This file splits V1 accordingly into

* `ComplexLanglandsQuotientStatement` (Langlands classification, Knapp 1994, Theorem 4), already
  stated in `ComplexGenericParameterReduction`: every irreducible admissible module receives a
  nonzero intertwining map from the `U(n)`-finite functions of the standard module of `n`
  complex characters in the Langlands order;
* `ComplexLargeLanglandsQuotientInjectiveStatement` (Vogan 1978, Theorem 6.2, proof of
  (a) ⇒ (f)): every such nonzero intertwining map onto an irreducible admissible large module
  is injective.

`complexLargePrincipalSeriesReduction` proves that the two imply V1, and
`complexLargeLanglandsQuotientInjective_of_principalSeries` proves that the second statement
follows from V1 and `ComplexStandardSurjectionInjectiveStatement` (Knapp 1994, Theorem 4).
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

/-- Vogan's theorem (1978, Theorem 6.2, proof of (a) ⇒ (f)) for `GL_n(ℂ)` and the Library's
standard modules: the standard module of a large Langlands quotient is irreducible. In the
form used here: if `(ρ, π)` is an irreducible admissible large `(𝔤𝔩_n(ℂ), U(n))`-module and
`ds` is a list of `n` complex characters in the Langlands order, then every nonzero
intertwining map from the `U(n)`-finite functions of the standard module of `ds` into
`(ρ, π)` is injective. -/
def ComplexLargeLanglandsQuotientInjectiveStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ds : List ComplexCharacterData)
    (A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsComplexLargeGKModule n π → ds.length = n → IsComplexLanglandsOrdered ds → A ≠ 0 →
        IsComplexStandardIntertwining n ρ π ds A → Function.Injective A

/-- The Langlands classification and Vogan's injectivity theorem imply
`ComplexLargePrincipalSeriesStatement`. -/
def ComplexLargePrincipalSeriesReductionStatement : Prop :=
  ComplexLanglandsQuotientStatement.{uV} →
    ComplexLargeLanglandsQuotientInjectiveStatement.{uV} →
      ComplexLargePrincipalSeriesStatement.{uV}

/-- Proof of the reduction: the Langlands classification gives a nonzero intertwining map from
a Langlands-ordered standard module, and Vogan's theorem makes it injective. -/
theorem complexLargePrincipalSeriesReduction :
    ComplexLargePrincipalSeriesReductionStatement.{uV} := by
  intro hLQ hV n V _ _ ρ π hgk hirr hadm hlarge
  obtain ⟨ds, hlen, hord, A, h0, hA⟩ := hLQ n V ρ π hgk hirr hadm
  exact ⟨ds, hlen, A, hV n V ρ π ds A hgk hirr hadm hlarge hlen hord h0 hA, hA⟩

/-- Conversely, `ComplexLargeLanglandsQuotientInjectiveStatement` follows from
`ComplexLargePrincipalSeriesStatement` and `ComplexStandardSurjectionInjectiveStatement`: a
nonzero intertwining map into an irreducible module is surjective, a large module has a
standard-module parameter, and then the surjection from a Langlands-ordered standard module
is injective. So the new statement asks for nothing beyond what these two statements already
assert. -/
theorem complexLargeLanglandsQuotientInjective_of_principalSeries
    (hP : ComplexLargePrincipalSeriesStatement.{uV})
    (hS : ComplexStandardSurjectionInjectiveStatement.{uV}) :
    ComplexLargeLanglandsQuotientInjectiveStatement.{uV} := by
  intro n V _ _ ρ π ds A hgk hirr hadm hlarge hlen hord h0 hA
  exact hS n V ρ π ds A hgk hirr hadm (hP n V ρ π hgk hirr hadm hlarge) hlen hord
    (surjective_of_isComplexStandardIntertwining n hirr hA h0) hA

end Langlands.Archimedean
