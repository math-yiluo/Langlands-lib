# Irreducible admissible generic `(𝔤𝔩_n(ℝ), O(n))`-modules have standard-module parameters

Module: `Langlands.Representation.Archimedean.RealGenericStandardParameterProof`.

## What is proved

`Langlands.Archimedean.realGenericStandardParameter :
RealGenericStandardParameterStatement.{uV}` proves the Library statement
`RealGenericStandardParameterStatement` (module `Langlands.Representation.Archimedean.GKModule`).
Fix `n : ℕ`, a complex vector space `V : Type uV`, a representation `ρ` of
`Matrix.unitaryGroup (Fin n) ℝ = O(n)` on `V` and a Lie algebra map
`π : ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ) → End_ℂ(V)`. Assume `IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π`,
`IsAdmissibleGKModule ρ` and `IsRealGenericGKModule n π`. Then there is a list
`ds : List RealBlock` with `HasRealStandardParameter n ρ π ds`. That is, `realRank ds = n`, and
there is an injective complex-linear map `A` from the `O(n)`-finite functions of the Library's
standard module `realStandardModule n ds` into `V`. This map carries right translation by
`k ∈ O(n)` to `ρ(k)` and the right derivative along a real matrix `X` to `π(1 ⊗ X)`.

The theorem keeps every quantifier and the universe `uV` of the statement, and adds no
hypotheses. `lean_check` reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The module also proves two intermediate theorems, both without added hypotheses:

* `realLanglandsQuotient_of_principalSeries : RealLanglandsQuotientStatement.{uV}`;
* `realGenericLanglandsQuotientInjective_of_large :
  RealGenericLanglandsQuotientInjectiveStatement.{uV}`.

These are the two premises of the published reduction in
[`RealGenericParameterReduction`](RealGenericParameterReduction.md). Their names carry a suffix
so that they do not clash with the proofs of the same statements in other modules
(`realLanglandsQuotient` in `RealLanglandsQuotientProof`, `realGenericLanglandsQuotientInjective`
in `RealGenericLanglandsQuotientInjective`).

## Proof

The module adds no argument of its own. Every name below is in the namespace
`Langlands.Archimedean`. The proof is three applications of published reductions:

```lean
theorem realLanglandsQuotient_of_principalSeries : RealLanglandsQuotientStatement.{uV} :=
  realLanglandsQuotientReduction realPrincipalSeriesQuotient realLanglandsFromPrincipalSeries

theorem realGenericLanglandsQuotientInjective_of_large :
    RealGenericLanglandsQuotientInjectiveStatement.{uV} :=
  realGenericLargeReduction InfinitesimalCharacter.realGKModuleInfinitesimalCharacter
    Kostant.realWhittakerMaximallyFaithful realLargeLanglandsQuotientInjective

theorem realGenericStandardParameter : RealGenericStandardParameterStatement.{uV} :=
  realGenericStandardParameterReduction realLanglandsQuotient_of_principalSeries
    realGenericLanglandsQuotientInjective_of_large
```

### 1. The Langlands quotient (premise S_A)

`RealLanglandsQuotientStatement` says that every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module receives a nonzero intertwiner (`IsRealStandardIntertwiner`) from the
`O(n)`-finite functions of `realStandardModule n ds`. Here `ds` is a list of real blocks of
total rank `n` in Langlands order (`IsRealLanglandsOrdered`: the real parts of the block
exponents do not increase).

* `realLanglandsQuotientReduction` (module
  [`RealLanglandsQuotientReduction`](RealLanglandsQuotientReduction.md)) proves
  `RealPrincipalSeriesQuotientStatement → RealLanglandsFromPrincipalSeriesStatement →
  RealLanglandsQuotientStatement`.
* `realPrincipalSeriesQuotient` (module
  [`RealPrincipalSeriesQuotientProof`](RealPrincipalSeriesQuotientProof.md)) proves the first
  premise. This is Casselman's subrepresentation theorem in quotient form: the module receives a
  nonzero intertwiner from the `O(n)`-finite principal series of some `n` characters of `ℝ^×`,
  in some order.
* `realLanglandsFromPrincipalSeries` (module
  [`RealLanglandsFromPrincipalSeriesProof`](RealLanglandsFromPrincipalSeriesProof.md)) proves the
  second premise. Starting from such a principal-series intertwiner, it repeatedly either
  exchanges two adjacent blocks or replaces them by other blocks, keeping a nonzero intertwiner
  into the same module at each step, until the list is in Langlands order.

### 2. Injectivity for a generic module (premise S_B)

`RealGenericLanglandsQuotientInjectiveStatement` says the following. Let the module be
irreducible, admissible and generic (`IsRealGenericGKModule`), and let `ds` have total rank `n`
and be in Langlands order. Then every nonzero intertwiner from the `O(n)`-finite functions of
`realStandardModule n ds` into the module is injective.

* `realGenericLargeReduction` (module [`RealGenericLargeReduction`](RealGenericLargeReduction.md))
  proves that S_B follows from three statements. The module has an infinitesimal character,
  so by Kostant's theorem genericity makes it maximally faithful, and then Vogan's theorem applies.
* `InfinitesimalCharacter.realGKModuleInfinitesimalCharacter` (module
  [`RealGKInfinitesimalCharacter`](RealGKInfinitesimalCharacter.md)) proves
  `RealGKModuleInfinitesimalCharacterStatement`: the center of `U(𝔤)` acts by scalars on an
  irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module.
* `Kostant.realWhittakerMaximallyFaithful` (module
  [`RealWhittakerMaximallyFaithfulProof`](RealWhittakerMaximallyFaithfulProof.md)) proves
  `RealWhittakerMaximallyFaithfulStatement`. This is Kostant's theorem (Kostant 1978, Theorem 3.9),
  proved along Matumoto's route (1987). A module with an infinitesimal character and a nonzero
  algebraic Whittaker functional for a nondegenerate character is maximally faithful.
* `realLargeLanglandsQuotientInjective` (module
  [`RealLargeLanglandsQuotientInjectiveProof`](RealLargeLanglandsQuotientInjectiveProof.md))
  proves `RealLargeLanglandsQuotientInjectiveStatement`. This is the injectivity consequence of
  Vogan's theorem (Vogan 1978, Theorem 6.2, proof of (a) ⇒ (f)) for `GL_n(ℝ)`. If the module is
  maximally faithful, every nonzero intertwiner from a Langlands-ordered standard module into
  it is injective.

### 3. The target

`realGenericStandardParameterReduction` (module
[`RealGenericParameterReduction`](RealGenericParameterReduction.md)) proves
`RealLanglandsQuotientStatement → RealGenericLanglandsQuotientInjectiveStatement →
RealGenericStandardParameterStatement`. Given the module, S_A supplies a Langlands-ordered `ds` of
total rank `n` and a nonzero intertwiner `B`. Since the module is generic, S_B makes `B`
injective. Then `realRank ds = n`, the injectivity of `B` and its intertwining properties are
exactly the clauses of `HasRealStandardParameter n ρ π ds`.

## Prerequisites

The route has four prerequisites that must be proved or imported as proved Library
theorems. Each is discharged by a theorem above, not kept as a premise:

* the Langlands classification in the block form of the Library's standard modules (Knapp 1994,
  Theorems 1–2), existence half: step 1;
* the passage from a nonzero algebraic Whittaker functional (`IsRealGenericGKModule`) to
  genericity in the form the argument needs, namely maximal faithfulness (Kostant 1978,
  Matumoto 1987): `realGKModuleInfinitesimalCharacter` and `realWhittakerMaximallyFaithful`
  in step 2;
* the irreducibility of the standard module of a generic Langlands quotient (Vogan 1978, as
  reported by Casselman–Shahidi 1998, p. 562), in the form of injectivity of the map onto the
  quotient: `realLargeLanglandsQuotientInjective` in step 2. Jacquet 2009,
  Theorem 2.1 and Remark 2.2 are not the source of this fact. As
  [`RealGenericParameterReduction.md`](RealGenericParameterReduction.md) records, those passages
  are about Rankin–Selberg integrals, so the cited form here is Vogan's;
* the identification of `realStandardModule n ds` and its `O(n)`-finite part with the classical
  standard module and its Harish-Chandra module. Every theorem used above is stated and proved
  for the Library's `realStandardModule n ds` and its `O(n)`-finite functions directly, so the
  proof needs no comparison isomorphism as a premise.
  [`StandardModule.md`](StandardModule.md) explains why this model is the classical normalized
  induced representation.

The proof does not use the uniqueness half of the Langlands classification.
