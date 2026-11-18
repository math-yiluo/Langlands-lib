# Irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-modules have standard-module parameters

`Langlands.Archimedean.complexGenericStandardParameter :
ComplexGenericStandardParameterStatement.{uV}` proves the Library statement
`ComplexGenericStandardParameterStatement` (module
`Langlands.Representation.Archimedean.GKModule`). The statement says: for every `n`, every
irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` on a complex vector space
`V : Type uV` has the standard-module parameter of some list `ds` of complex characters
(`HasComplexStandardParameter n ρ π ds`). That is, `ds.length = n`, and some injective
`(𝔤, K)`-intertwining map sends the `U(n)`-finite functions of the principal series
`complexStandardModule n ds` onto `V`.

The theorem adds no hypotheses and keeps the universe `uV` of the target.

## Proof

The proof is a single term that combines three Library theorems.

1. `complexGenericStandardParameter_of_large` (module
   `Langlands.Representation.Archimedean.ComplexGenericStandardInjectiveReduction`) proves
   `ComplexGenericLargeStatement → ComplexLargePrincipalSeriesStatement →
   ComplexGenericStandardParameterStatement`. Given an irreducible admissible generic module,
   it applies the first premise to see that the module is large (`IsComplexLargeGKModule`).
   It then applies the second premise to get a standard-module parameter.
2. `complexGenericLarge : ComplexGenericLargeStatement` (module
   `Langlands.Representation.Archimedean.ComplexGenericLargeProof`): every irreducible
   admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module is large. This is the complex case of Kostant's
   theorem (Kostant, *On Whittaker vectors and representation theory*, Invent. Math. 48 (1978),
   Theorem 3.9), proved in the Library along Matumoto's route.
3. `complexLargePrincipalSeries : ComplexLargePrincipalSeriesStatement` (module
   `Langlands.Representation.Archimedean.ComplexLargePrincipalSeriesProof`): every irreducible
   admissible large `(𝔤𝔩_n(ℂ), U(n))`-module has the standard-module parameter of some list of
   complex characters. This is Vogan's theorem (Vogan, *Gelfand–Kirillov dimension for
   Harish-Chandra modules*, Invent. Math. 48 (1978), Theorem 6.2 (a) ⇒ (f)) for `GL_n(ℂ)`. The
   Library proves it from the Langlands classification (`complexLanglandsQuotient`) and from
   the fact that a nonzero intertwining map from a Langlands-ordered standard module into an
   irreducible admissible large module is injective.

Applying (1) to (2) and (3) gives the target.

## Relation to the earlier reduction

`complexGenericParameterReduction` (module
`Langlands.Representation.Archimedean.ComplexGenericParameterReduction`) reduces the target to
the Langlands classification statement `ComplexLanglandsQuotientStatement` and the injectivity
statement `ComplexGenericStandardInjectiveStatement`. The proof here does not use that
reduction. It goes through largeness instead, which needs neither of those statements directly.
