# Proof that the actual relative Weyl group is a finite Coxeter group

`relativeWeylCoxeter` proves the published proposition
`RelativeWeylCoxeterStatement.{u}` (module
`Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement`) exactly, at an
arbitrary universe `u`. Fix any field `k`, connected reductive `G` over `Spec k`,
maximal split torus `i : T.toGrp ⟶ G` and cocharacter `ν` with
`IsGenericCocharacter i ν`. The theorem gives `HasRelativeWeylCoxeterSystem i ν`:

- `relativeWeylGroup i = N(k)/Z(k)` is finite;
- `SimpleRoot i ν` is finite;
- some Coxeter matrix and Coxeter system on `relativeWeylGroup i`, labelled by
  `SimpleRoot i ν`, satisfy all five conditions of
  `IsRelativeWeylCoxeterRealization`.

No hypothesis is added to the statement. Rank zero (no relative roots, so empty
labels and the trivial group) and nonreduced relative roots are covered, because
every step below is proved for an arbitrary finite, possibly empty and possibly
nonreduced, set of actual relative roots.

## Implemented proof

The theorem is a composition of three published unconditional theorems and two
published implications.

1. `rootRankOneFactorization : RootRankOneFactorizationStatement.{u}` (module
   `Rational.RootRankOneFactorizationProof`). For every relative root `a` and
   nonidentity rational point `u` of the actual root subgroup of `a`, it gives a
   unique opposite factor pair `(u′, u′′)` such that `u′ * u * u′′` normalizes
   the torus. Its proof uses reductivity of the identity component of every
   full character-kernel centralizer
   (`RelativeRoot.kernelCentralizerComponentReductive`) and a rank-one parabolic
   double-coset covering inside that component.
2. `relativeRootSystemStatement_of_rootRankOneFactorizationStatement` (module
   `Rational.RootSystemFromFactorPairs`) turns item 1 into
   `RelativeRootSystemStatement.{u}`. The opposite pairs give
   `RelativeRootReflectionData.ofOppositeFactorPairs`, built by
   `RelativeRootReflectionData.ofKernelCentralizingRepresentatives`. For each
   root `a` it chooses a normalizing point that sends `a` to `-a` and
   centralizes the full scheme-theoretic kernel of `a`. That gives an integral
   cocharacter pairing to `2` with `a` and the lattice reflection formula on all
   of `X*(T)`. The published unconditional `hasTrivialPositiveRootStabilizer`
   and `RelativeRootReflectionData.hasRelativeRootSystem_of_positive_stabilizer`
   then construct the evaluation root pairing and prove the Weyl image and
   faithfulness parts of `HasRelativeRootSystem i`.
3. `RootGeneratedCentralizerStructuralPremises.relativeWeylCoxeter` (module
   `Rational.RootGeneratedCentralizerReduction`) takes the conjunction of
   `RelativeRootSystemStatement.{u}` and `RootRankOneFactorizationStatement.{u}`
   and proves `RelativeWeylCoxeterStatement.{u}`. It derives
   `RelativeRootReflectionExistenceStatement.{u}` from the rank-one statement
   (`relativeRootReflectionExistence_of_rootRankOneFactorization`). It then
   applies `relativeWeylCoxeterStatement_of_rootPairingWeylCoxeterStatement`
   (module `Rational.RelativeWeylCoxeterReduction`) to the root system
   statement, this reflection existence statement and Aubert's published
   abstract Coxeter theorem `Langlands.Group.rootPairingWeylCoxeterStatement_proof`.

`relativeWeylCoxeter` supplies item 3 with the pair formed by items 2 and 1.

Inside item 3, the published
`RelativeRootReflectionData.hasRelativeWeylCoxeterSystem_of_rootPairing`
(module `Rational.RelativeWeylCoxeterAssembly`) does the transport. The abstract
theorem gives a Coxeter system on the Weyl group of the evaluation root pairing
on the rational root span. Its simple reflections are labelled by the base of
the linear form of `ν`, and it comes with the reduced inversion-count length
formula and the descent criterion. The root-system statement identifies this
Weyl group with `N(k)/Z(k)` through their common faithful action on the root
span. The base corresponds to `simpleRelativeRoots i ν`. The five conditions are
then read off as follows:

1. Each simple generator is the class of the chosen reflection representative,
   so it acts on every character by `χ ↦ χ - ⟨χ, a∨⟩ • a`.
2. The inversion set of a simple reflection is `{a}`, which handles positive
   roots other than `a` and `2a`.
3. The length/sign criterion is the transported descent criterion.
4. The length equals the number of reduced positive roots made negative.
5. Coxeter parabolic subgroups equal `standardRelativeWeylGroup`: one inclusion
   holds because the representatives centralize the root kernels, and the other
   by induction on length using a standard cocharacter.

Finiteness of `N(k)/Z(k)` and of the simple roots comes from the root-system
statement.

## The Milne errata warning

Milne's official errata (`milne-2017-algebraic-groups-errata-2026-11-02`, entry
"p.549") say that the classical proofs that the relative root system is a root
system (Borel–Tits 1965, Borel 1991, Springer 1998) are incomplete, and refer to
Conrad–Gabber–Prasad C.2.15. This Lean proof does not rely on those arguments.
The root-system axioms are proved directly from actual rational points of `G`:

- integrality and stability of the roots come from the normalizing products
  `u′ * u * u′′` of item 1, which centralize the full root kernels;
- generation and faithfulness come from the integral-averaging and
  generic-centralizer proof of `hasTrivialPositiveRootStabilizer`.

The rank-one input is the rank-one factorization that its statement attributes
to Kaletha–Prasad 2.11.17 and Conrad–Gabber–Prasad C.2.24(i),(iii). It is proved
in the Library, not assumed. Every step is machine-checked, and
`relativeWeylCoxeter` depends only on the axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Provenance

This is an internal composition of published Library results. It introduces no
new definitions and assumes none of `HasRelativeWeylCoxeterSystem`,
`HasRelativeRootSystem`, a Coxeter realization or a reflection-generation
theorem. The literature behind the statement is cited with exact locations in
the Markdown of `RelativeWeylCoxeterStatement` (Borel–Tits 5.3, 5.8, 5.15–5.17;
Renard V.3.4, V.3.7, V.4.6). The proof route above differs from Borel–Tits in
the way just explained.
