import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientUniqueProof
import Langlands.Representation.Archimedean.ComplexStandardPermutationProof
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.Archimedean.ComplexLargePrincipalSeriesProof

/-!
# Langlands-ordered standard modules onto irreducible modules: injectivity

`complexStandardSurjectionInjective` proves `ComplexStandardSurjectionInjectiveStatement`
(Knapp 1994, Theorem 4 (a) and (c)): a surjective intertwining map from the `U(n)`-finite
functions of the standard module of a Langlands-ordered list of `n` complex characters onto an
irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module that has a standard-module parameter is
injective.

The module records both halves of Knapp 1994, Theorem 4, that the objective names:

* (a) for one list: `ComplexStandardSurjectionInjectiveProof.langlandsQuotient` derives the
  unique irreducible quotient of a Langlands-ordered standard module from the Library theorem
  `ComplexLargePrincipalSeriesProof.standardLanglandsQuotient` (largest proper
  `(𝔤, K)`-submodule `R`): `R` is a maximal `(𝔤, K)`-submodule, and every nonzero intertwining
  map into an irreducible `(𝔤𝔩_n(ℂ), U(n))`-module has kernel `R`;
* (c) the parameter comparison for two lists: the Library theorem
  `complexLanglandsQuotientUnique` (LU).

The target theorem applies the Library reduction `complexStandardSurjectionInjectiveReduction`
(LU → PI → NZ → target) to `complexLanglandsQuotientUnique` (LU),
`complexStandardPermutation` (PI) and `complexStandardNontrivial` (NZ). See the paired Markdown.
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

namespace ComplexStandardSurjectionInjectiveProof

/-- **The Langlands quotient of one Langlands-ordered list** (Knapp 1994, Theorem 4 (a), in the
algebraic form of the Library's `(𝔤, K)`-module predicates). Let `ds` be a list of `n` complex
characters in the Langlands order and `X(ds)` the `U(n)`-finite functions of its standard
module. There is a `(𝔤, K)`-submodule `R ≠ X(ds)` such that

* `R` is maximal: every `(𝔤, K)`-submodule containing `R` is `R` or `X(ds)`, so the quotient
  `X(ds) / R` is irreducible;
* every nonzero intertwining map `A` from `X(ds)` into an irreducible `(𝔤𝔩_n(ℂ), U(n))`-module
  has kernel `R`, so every irreducible quotient of `X(ds)` is `X(ds) / R`. -/
theorem langlandsQuotient (n : ℕ) (ds : List ComplexCharacterData) (hlen : ds.length = n)
    (hord : IsComplexLanglandsOrdered ds) :
    ∃ R : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
      IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) R ∧ R ≠ ⊤ ∧
      (∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
        IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W → R ≤ W →
          W = R ∨ W = ⊤) ∧
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
        (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
        (A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V),
        IsIrreducibleGKModule ρ π → IsComplexStandardIntertwining n ρ π ds A → A ≠ 0 →
          LinearMap.ker A = R := by
  obtain ⟨R, hR, hRtop, hRmax⟩ :=
    ComplexLargePrincipalSeriesProof.standardLanglandsQuotient n ds hlen hord
  refine ⟨R, hR, hRtop, fun W hW hRW => ?_, fun V _ _ ρ π A hirr hA hA0 => ?_⟩
  · by_cases hWtop : W = ⊤
    · exact Or.inr hWtop
    · exact Or.inl (le_antisymm (hRmax W hW hWtop) hRW)
  · exact (eq_ker_of_largest_proper hA.map_complexStandardRep hA.map_complexStandardLie hirr
      hA0 hR hRtop hRmax).symm

end ComplexStandardSurjectionInjectiveProof

/-- **Injectivity of surjections from Langlands-ordered standard modules** (Knapp 1994,
Theorem 4 (a) and (c)): a surjective intertwining map from the `U(n)`-finite functions of the
standard module of a Langlands-ordered list of `n` complex characters onto an irreducible
admissible `(𝔤𝔩_n(ℂ), U(n))`-module with a standard-module parameter is injective. -/
theorem complexStandardSurjectionInjective : ComplexStandardSurjectionInjectiveStatement.{uV} :=
  complexStandardSurjectionInjectiveReduction complexLanglandsQuotientUnique
    complexStandardPermutation complexStandardNontrivial

end Langlands.Archimedean
