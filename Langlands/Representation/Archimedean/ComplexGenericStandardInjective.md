# Generic standard modules of `GL_n(ℂ)` are irreducible

`Langlands.Archimedean.complexGenericStandardInjective :
ComplexGenericStandardInjectiveStatement.{uV}` proves the Library statement
`ComplexGenericStandardInjectiveStatement` (module
`Langlands.Representation.Archimedean.ComplexGenericParameterReduction`).

The statement says the following. Fix `n : ℕ`, a complex vector space `V : Type uV`, a
representation `ρ` of `U(n)` on `V` and an action `π` of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` on `V`. Assume that
`(ρ, π)` is an irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module. Let `ds` be a list of
`n` complex characters in the Langlands order (`IsComplexLanglandsOrdered`). Let `A` be a
surjective intertwining map (`IsComplexStandardIntertwining`) from the `U(n)`-finite functions
of `complexStandardModule n ds` onto `V`. Then `A` is injective. So the standard module of a
generic Langlands quotient is irreducible (Vogan 1978; Jacquet 2009, p. 9, refers to Vogan 1978
for an algebraic proof).

The theorem keeps every quantifier and the universe `uV` of the target and adds no hypotheses.

## Proof

The Lean proof introduces all the data and hypotheses of the statement and then uses two proved
Library theorems.

1. **The module is large.** `complexGenericLarge : ComplexGenericLargeStatement` (module
   `Langlands.Representation.Archimedean.ComplexGenericLargeProof`) is Kostant's theorem
   (Kostant 1978, Theorem 3.9; Matumoto 1987, Corollary 5) for this setting. Applied to the
   hypotheses `IsComplexGKModule`, `IsIrreducibleGKModule`, `IsAdmissibleGKModule` and
   `IsComplexGenericGKModule`, it gives `IsComplexLargeGKModule n π`.
2. **`A` is nonzero.** The first component of `IsIrreducibleGKModule ρ π` is `Nontrivial V`.
   So `V` has a vector `v ≠ 0`. By surjectivity `v = A f` for some `f`. If `A` were `0`, then
   `v = A f = 0`, a contradiction.
3. **Vogan's injectivity theorem.**
   `ComplexLargePrincipalSeriesProof.largeLanglandsQuotientInjective :
   ComplexLargeLanglandsQuotientInjectiveStatement` (module
   `Langlands.Representation.Archimedean.ComplexLargePrincipalSeriesProof`; Vogan 1978,
   Theorem 6.2, proof of (a) ⇒ (f)) states the following. Every nonzero intertwining map from the `U(n)`-finite
   functions of the standard module of a Langlands-ordered list of `n` complex characters into an
   irreducible admissible large `(𝔤𝔩_n(ℂ), U(n))`-module is injective. Its hypotheses are the
   three module hypotheses, largeness from step 1, `ds.length = n`, the Langlands order of `ds`,
   `A ≠ 0` from step 2 and the intertwining property of `A`. It gives `Function.Injective A`.

## Relation to the published reduction

The Library reduction `complexGenericStandardInjectiveReduction` (module
`Langlands.Representation.Archimedean.ComplexGenericStandardInjectiveReduction`) derives the
target from `ComplexGenericLargeStatement`, `ComplexLargePrincipalSeriesStatement` and
`ComplexStandardSurjectionInjectiveStatement`. This proof does not use that reduction. It uses
neither `ComplexLargePrincipalSeriesStatement` nor `ComplexStandardSurjectionInjectiveStatement`.
Instead it applies Vogan's injectivity theorem directly. The Library proves that theorem on the
way to `ComplexLargePrincipalSeriesStatement`.
