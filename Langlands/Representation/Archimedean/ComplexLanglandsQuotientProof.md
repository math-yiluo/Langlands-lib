# Proof of the Langlands quotient statement for `(𝔤𝔩_n(ℂ), U(n))`-modules

Lean module: `Langlands.Representation.Archimedean.ComplexLanglandsQuotientProof`
(namespace `Langlands.Archimedean`, universe `uV` for the module carrier).

## Statement proved

```lean
theorem complexLanglandsQuotient : ComplexLanglandsQuotientStatement.{uV}
```

`ComplexLanglandsQuotientStatement.{uV}` is the Library statement of module
`Langlands.Representation.Archimedean.ComplexGenericParameterReduction`. For every `n : ℕ`,
every complex vector space `V : Type uV`, every
`ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V` and every Lie algebra map
`π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V` such that `(ρ, π)` is a
`(𝔤𝔩_n(ℂ), U(n))`-module (`IsComplexGKModule n ρ π`) that is irreducible
(`IsIrreducibleGKModule ρ π`) and admissible (`IsAdmissibleGKModule ρ`), it gives

* a list `ds : List ComplexCharacterData` with `ds.length = n`,
* the Langlands order `IsComplexLanglandsOrdered ds`: the real parts of the exponents do not
  increase along the list,
* a nonzero linear map
  `A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V` with
  `IsComplexStandardIntertwining n ρ π ds A`.

This is the existence half of the Langlands classification of irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-modules in quotient form (Knapp 1994, Theorem 4 (a)–(b), p. 405, due to
Zhelobenko and Naimark). The theorem adds no
hypotheses to the statement and keeps its universe `uV`.

## Proof

The proof is a composition of four Library theorems; it contains no new mathematics.

The Library theorem `complexLanglandsQuotientReduction` (module
`Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction`) proves
`ComplexLanglandsQuotientReductionStatement.{uV}`, the implication

`ComplexLanglandsSubrepresentationStatement.{uV} → ComplexContragredientStatement.{uV} →
ComplexStandardDualityStatement → ComplexLanglandsQuotientStatement.{uV}`.

Its proof passes to the `U(n)`-finite contragredient `W` of `V` (S2), embeds `W` into the
`U(n)`-finite functions of a standard module of characters `ds'` with non-decreasing exponent
real parts (S1 applied to `W`), and then uses the duality pairing `Q` between the standard
modules of `ds` (the pointwise inverse characters of `ds'`, whose exponents are negated and so
have non-increasing real parts) and of `ds'` (S3) to turn the embedding into a nonzero
intertwining map `A` from the standard module of `ds` into `V`.

The three premises are discharged by these Library theorems:

* S1, `ComplexLanglandsSubrepresentationStatement.{uV}`: `complexLanglandsSubrepresentation`
  (module `Langlands.Representation.Archimedean.ComplexLanglandsSubrepresentationProof`).
* S2, `ComplexContragredientStatement.{uV}`:
  `ComplexContragredient.complexContragredientStatement` (module
  `Langlands.Representation.Archimedean.ComplexContragredientProof`).
* S3, `ComplexStandardDualityStatement`: `complexStandardDuality` (module
  `Langlands.Representation.Archimedean.ComplexStandardDualityProof`).

The module proves this in two steps:

1. `complexLanglandsQuotient_of_subrepresentation (hS1 : ComplexLanglandsSubrepresentationStatement.{uV}) :
   ComplexLanglandsQuotientStatement.{uV}` is
   `complexLanglandsQuotientReduction hS1 ComplexContragredient.complexContragredientStatement
   complexStandardDuality`: the target follows from S1 alone, with S2 and S3 discharged.
2. `complexLanglandsQuotient` applies this to `complexLanglandsSubrepresentation`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Reference

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in Motives
  (Seattle, 1991), Proc. Sympos. Pure Math. 55, Part 2, AMS, 1994, Theorem 4 (a)–(b), p. 405
  (literature ID `knapp-1994-archimedean-llc`). The Lean proof follows the reduction above, not
  Knapp's route.
