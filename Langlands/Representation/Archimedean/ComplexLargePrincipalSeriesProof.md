# Proof: large irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-modules are principal series

Lean module: `Langlands.Representation.Archimedean.ComplexLargePrincipalSeriesProof`
(namespace `Langlands.Archimedean`, universe `uV` for the module carrier).

## Statement proved

```lean
theorem complexLargePrincipalSeries : ComplexLargePrincipalSeriesStatement.{uV}
```

`ComplexLargePrincipalSeriesStatement.{uV}` is the Library statement of module
`Langlands.Representation.Archimedean.ComplexGenericStandardInjectiveReduction`. Fix `n : ℕ`, a
complex vector space `V : Type uV`, a representation
`ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V` and a Lie algebra map
`π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V`. Suppose `(ρ, π)` is a
`(𝔤𝔩_n(ℂ), U(n))`-module (`IsComplexGKModule n ρ π`) that is irreducible
(`IsIrreducibleGKModule ρ π`), admissible (`IsAdmissibleGKModule ρ`) and large
(`IsComplexLargeGKModule n π`). Then there is a list `ds : List ComplexCharacterData` with
`HasComplexStandardParameter n ρ π ds`.

This is Vogan 1978, Theorem 6.2, (a) ⇒ (f), for `GL_n(ℂ)`. The statement's Markdown gives the
source. The theorem adds no hypotheses and keeps the universe `uV`.

## Proof

The proof composes proved Library theorems. It contains no new mathematics. It has three steps,
and the first two are auxiliary theorems in the namespace
`Langlands.Archimedean.ComplexLargePrincipalSeriesProof`.

1. **Largest proper submodule.** `standardLanglandsQuotient : ComplexStandardLanglandsQuotientStatement`
   is `complexBlockLanglandsQuotient complexBlockChartIntegrable complexBlockParabolicIntegration
   complexTemperedStandardIrreducible`. For a list `ds` of `n` complex characters in the
   Langlands order, it gives a largest proper `(𝔤, K)`-submodule `R` of the `U(n)`-finite
   functions of `complexStandardModule n ds`. The Library theorem `complexBlockLanglandsQuotient`
   (module `ComplexBlockLanglandsQuotient`) proves the implication
   `ComplexBlockChartIntegrableStatement → ComplexBlockParabolicIntegrationStatement →
   ComplexTemperedStandardIrreducibleStatement → ComplexStandardLanglandsQuotientStatement`.
   Its premises are discharged by `complexBlockChartIntegrable` (module
   `ComplexBlockChartIntegralProof`), `complexBlockParabolicIntegration` (module
   `ComplexBlockParabolicIntegrationProof`) and `complexTemperedStandardIrreducible` (module
   `ComplexTemperedStandardIrreducibleProof`).
2. **Injectivity.** `largeLanglandsQuotientInjective : ComplexLargeLanglandsQuotientInjectiveStatement.{uV}`
   is `complexLargeStandardIrreducibleReduction standardLanglandsQuotient
   complexLargeStandardIrreducible`. It says that every nonzero intertwining map `A` from the
   `U(n)`-finite functions of a Langlands-ordered standard module into an irreducible admissible
   large `(𝔤𝔩_n(ℂ), U(n))`-module is injective. The Library reduction
   `complexLargeStandardIrreducibleReduction` (module `ComplexLargeStandardIrreducibleReduction`)
   works as follows. `A` is onto, so its kernel is the largest proper submodule `R` from step 1.
   Because `V` is large, the quotient by `R` is maximally faithful. Vogan's irreducibility theorem
   `complexLargeStandardIrreducible` (module `ComplexLargeStandardIrreducibleProof`) then gives
   `R = ⊥`.
3. **Assembly.** `complexLargePrincipalSeries` is `complexLargePrincipalSeriesReduction
   complexLanglandsQuotient ComplexLargePrincipalSeriesProof.largeLanglandsQuotientInjective`.
   The Library reduction `complexLargePrincipalSeriesReduction` is in module
   `ComplexLargePrincipalSeriesReduction`. The Langlands classification `complexLanglandsQuotient`
   (module `ComplexLanglandsQuotientProof`) gives a Langlands-ordered `ds` of length `n` and a
   nonzero intertwining map `A` from its standard module into `V`. By step 2, `A` is injective,
   and this is the parameter `HasComplexStandardParameter n ρ π ds`.

`lean_check` reports that the theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Reference

* D. A. Vogan, *Gelfand–Kirillov dimension for Harish-Chandra modules*, Invent. Math. 48 (1978),
  75–98, Theorem 6.2 and its proof of (a) ⇒ (f), pp. 89–93. The Lean proof follows the Library
  reductions above, not Vogan's translation and τ-invariant argument.

The complex standard quotient uses the standalone proof `Langlands.Archimedean.complexStandardLanglandsQuotient`.
