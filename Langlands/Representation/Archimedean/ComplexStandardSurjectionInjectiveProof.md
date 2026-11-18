# Langlands-ordered standard modules onto irreducible modules: injectivity

Module `Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveProof`, namespace
`Langlands.Archimedean`, universe `uV` for the module carrier. Worker 86 wrote it for Task 6759
(`66a0707a-ea74-4cb9-8555-76b129898fd5`).

## Results

```
theorem complexStandardSurjectionInjective : ComplexStandardSurjectionInjectiveStatement.{uV}

theorem ComplexStandardSurjectionInjectiveProof.langlandsQuotient (n : ℕ)
    (ds : List ComplexCharacterData) (hlen : ds.length = n) (hord : IsComplexLanglandsOrdered ds) :
    ∃ R, IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) R ∧ R ≠ ⊤ ∧
      (∀ W, IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W → R ≤ W →
        W = R ∨ W = ⊤) ∧
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] ρ π A,
        IsIrreducibleGKModule ρ π → IsComplexStandardIntertwining n ρ π ds A → A ≠ 0 →
          LinearMap.ker A = R
```

(In the second theorem `R` and `W` range over the `ℂ`-submodules of the `U(n)`-finite functions
of `complexStandardModule n ds`, and `ρ`, `π`, `A` have the types of the target statement below.)

**Target.** `Langlands.Archimedean.ComplexStandardSurjectionInjectiveStatement` is the Library
statement of module `Langlands.Representation.Archimedean.ComplexGenericStandardInjectiveReduction`.
Let `(ρ, π)` be an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module on a complex vector space
`V : Type uV` (`IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π`,
`IsAdmissibleGKModule ρ`) that has the standard-module parameter of some list `ds'` of complex
characters (`HasComplexStandardParameter n ρ π ds'`). Let `ds` be a list of `n` complex
characters in the Langlands order (`IsComplexLanglandsOrdered ds`: the real parts of the
exponents do not increase). Then every surjective linear map `A` from the `U(n)`-finite
functions of the standard module of `ds` onto `V` with `IsComplexStandardIntertwining n ρ π ds A`
is injective. `complexStandardSurjectionInjective` keeps the statement's universe `uV` and adds
no hypotheses.

**Theorem 4 (a) for one list.** Write `X(ds)` for the `U(n)`-finite functions of
`complexStandardModule n ds` with its `(𝔤𝔩_n(ℂ), U(n))`-action
`(complexStandardRep n ds, complexStandardLie n ds)`. This is the Harish-Chandra module of the
principal series `I(σ₁, …, σ_n)`. `langlandsQuotient` says that, for a Langlands-ordered list `ds`
of length `n`, `X(ds)` has a proper `(𝔤, K)`-submodule `R` with two properties:

* `R` is a maximal `(𝔤, K)`-submodule: every `(𝔤, K)`-submodule `W ⊇ R` is `R` or `X(ds)`.
  The `(𝔤, K)`-submodules of the quotient `X(ds) / R` correspond to the `(𝔤, K)`-submodules of
  `X(ds)` that contain `R`. Maximality therefore says that `X(ds) / R` is irreducible. This
  quotient is the Langlands quotient `J(σ)`. The Lean statement gives maximality directly and
  does not construct the quotient module. The Library's statements about quotients, such as
  `IsMaximallyFaithfulModulo`, follow the same convention.
* Every irreducible quotient of `X(ds)` is `X(ds) / R`: if `A` is a nonzero intertwining map
  (`IsComplexStandardIntertwining n ρ π ds A`) from `X(ds)` into an irreducible
  `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` on any `V : Type uV`, then `ker A = R`. A surjection onto a
  nontrivial module is nonzero. So every irreducible quotient `X(ds) / ker A ≅ V` has the
  same kernel `R`.

This is the uniqueness of the irreducible quotient in Knapp 1994, Theorem 4 (a), in the
algebraic form of the Library's `GKModule` predicates.

## Proof

### The target theorem

`complexStandardSurjectionInjective` is the term

```
complexStandardSurjectionInjectiveReduction complexLanglandsQuotientUnique
  complexStandardPermutation complexStandardNontrivial
```

It applies the Library reduction `complexStandardSurjectionInjectiveReduction` (module
`ComplexStandardSurjectionInjectiveReduction`), which proves
`ComplexStandardSurjectionInjectiveReductionStatement`: the target follows from three
statements. The proof supplies a Library theorem for each:

* `ComplexLanglandsQuotientUniqueStatement` (LU, the parameter comparison of Theorem 4 (c)):
  two Langlands-ordered lists of `n` complex characters whose standard modules both map nonzero
  into the same irreducible admissible module are permutations of each other. It is supplied by
  `complexLanglandsQuotientUnique` (module `ComplexLanglandsQuotientUniqueProof`), at the same
  universe `uV`.
* `ComplexStandardPermutationStatement` (PI): if the principal series `X(ds)` is irreducible
  and `es` is a permutation of `ds`, there is a bijective intertwining map `X(es) → X(ds)`.
  It is supplied by `complexStandardPermutation` (module `ComplexStandardPermutationProof`),
  whose proof compares finite `U(n)`-multiplicities. This is the alternative that the
  objective allows in place of equal composition factors.
* `ComplexStandardNontrivialStatement` (NZ): the `U(n)`-finite functions of the standard
  module of `n` complex characters form a nontrivial space. It is supplied by
  `complexStandardNontrivial` (module `ComplexStandardNontrivialProof`).

`ComplexStandardSurjectionInjectiveReduction.md` explains how the reduction combines the
three. In brief: the parameter of `V` gives a list `ds'` of `n` characters and an injective
intertwining map `B : X(ds') → V`. By NZ, `X(ds')` is nonzero and hence irreducible. Sorting
`ds'` gives a Langlands-ordered permutation `es`, and PI gives a bijective intertwining map
`T : X(es) → X(ds')`, so `B ∘ T` is nonzero. `A` is nonzero because `V` is nontrivial and `A`
is surjective. LU, applied to `A` and `B ∘ T`, shows that `ds` is a permutation of `es`, hence
of `ds'`. PI then gives a bijective intertwining map `X(ds) → X(ds')`, so `X(ds)` is
irreducible, and the nonzero map `A` out of the irreducible module `X(ds)` is injective.

### Theorem 4 (a): `langlandsQuotient`

1. **The submodule `R`.** The Library theorem
   `ComplexLargePrincipalSeriesProof.standardLanglandsQuotient :
   ComplexStandardLanglandsQuotientStatement` (module `ComplexLargePrincipalSeriesProof`) gives,
   for `ds` of length `n` in the Langlands order, a `(𝔤, K)`-submodule `R ≠ ⊤` of `X(ds)` that
   contains every proper `(𝔤, K)`-submodule. It is the Library's proof
   `complexBlockLanglandsQuotient complexBlockChartIntegrable complexBlockParabolicIntegration
   complexTemperedStandardIrreducible`. `ComplexLargePrincipalSeriesProof.md` and
   `ComplexBlockLanglandsQuotient.md` describe its proof.
2. **Maximality.** Let `W ⊇ R` be a `(𝔤, K)`-submodule. If `W = ⊤`, we are done. Otherwise `W`
   is proper, so `W ≤ R`, and `W = R` by antisymmetry.
3. **Every irreducible quotient has kernel `R`.** This is the Library lemma
   `eq_ker_of_largest_proper` (module `ComplexLargeStandardIrreducibleReduction`). It is
   applied with the `U(n)`- and `𝔤𝔩_n(ℂ)`-equivariance of `A` that
   `IsComplexStandardIntertwining.map_complexStandardRep` and
   `IsComplexStandardIntertwining.map_complexStandardLie` provide (same module). The kernel of
   `A` is a `(𝔤, K)`-submodule, and it is proper because `A ≠ 0`, so `ker A ≤ R`. The image
   `A(R)` is a `(𝔤, K)`-submodule of the irreducible `V`. If `A(R) = V`, then every `f` would
   satisfy `f - r ∈ ker A ⊆ R` for some `r ∈ R`, so `R = ⊤`, a contradiction. Hence `A(R) = 0`,
   that is, `R ≤ ker A`.

The target theorem does not use `langlandsQuotient`, because the reduction above proves
injectivity from LU, PI and NZ alone. The module states `langlandsQuotient` so that the
fixed-list half of Theorem 4 (a), which the objective lists among the prerequisites, is a proved
theorem here. Together with LU this gives Knapp's Theorem 4 (a) and the parameter comparison
of (c) in the Library's algebraic form.

`lean_check` (lake build) reports 0 errors and 0 warnings. Both theorems use only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The target is Knapp 1994, Theorem 4 (a) and (c), printed p. 405 (PDF p. 415), source
`knapp-1994-archimedean-llc`. Knapp attributes the theorem to Želobenko and Naimark. The target
is recorded in the form given in `ComplexGenericStandardInjectiveReduction.md`. Theorem 4 (a)
says that if the parameters satisfy `Re t₁ ≥ Re t₂ ≥ … ≥ Re t_n` (4.3), then `I(σ₁, …, σ_n)`
has a unique irreducible quotient `J(σ₁, …, σ_n)`. Theorem 4 (c) says that `J(σ)` and `J(σ')`
are infinitesimally equivalent exactly when `σ'` is a permutation of `σ`. `langlandsQuotient` is
the algebraic form of (a). It is derived here from the Library's largest proper submodule, and
the derivation is internal: steps 2 and 3 above. LU is the "only if" direction of (c).

This file adds no other mathematical content: the target theorem only composes the four Library
theorems named above. The literature behind each input is given in the Markdown of the
reduction and of the supplying modules.
