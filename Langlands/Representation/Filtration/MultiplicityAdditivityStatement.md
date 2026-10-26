# Additive Jordan–Hölder multiplicities for actual finite filtrations

Author: Worker 430. Coauthor: Worker 166, whose focused task specification
supplies the requested mathematical interface.
Provenance: internal derived algebraic content.

`Langlands.JordanHolderMultiplicityAdditivityStatement` is a conjunction of
seven proposition definitions in
`Langlands.Representation.Filtration.MultiplicityAdditivityStatement`.
This module states the claims. It supplies no proof of additivity,
finite length, monotonicity, or any representation-theoretic comparison.

## Existing objects and scope

The sole import is
`Langlands.Representation.Filtration.MultiplicityStatement`. Its definitions
are used unchanged:

- `ObjectRepFiltration A n` is an actual increasing chain of invariant
  subspaces, from zero to the whole representation, with `n` successive
  quotients. Its `gradedRepresentation i` is the actual quotient of the
  next subspace by the current one.
- `t.HasSimpleFactors` says that every actual graded representation of
  `t` is irreducible.
- `t.factorMultiplicity τ` counts indices of factors equivalent to `τ`
  through actual `Representation.Equiv`s.
- `HasCompositionSeriesLength A N` supplies an actual composition series
  of `A` with `N` factors.
- `HasJordanHolderMultiplicity A τ M` supplies an actual composition
  series of `A` whose count of factors equivalent to `τ` is `M`.

All clauses quantify over a field `k : Type uK` and a monoid `G : Type uG`.
The representation carriers `A`, `B`, `C`, and `τ` have independent
universes `uA`, `uB`, `uC`, and `uT`. The aggregate proposition retains all
six independent universe parameters. Clauses needing fewer representations
retain the corresponding subset of these universes. No algebraic closure,
group inverse, smoothness, admissibility, finite dimension, or irreducibility
of `τ` is assumed.

The numerical predicates are existential statements about actual finite
series. No total multiplicity function is defined by choosing a series.
Every conclusion asserting a count also asserts existence of a finite
composition series through the unchanged predicate, or supplies the series
explicitly. Thus the assertions cannot be satisfied merely because two
finite-series predicates are both false.

## The seven claims

1. `JordanHolderFiltrationAdditivityStatement` takes any supplied
   `s : ObjectRepFiltration A n` and functions
   `lengths counts : Fin n → ℕ`. For every graded piece, the hypothesis
   supplies an actual composition series of length `lengths i` with
   multiplicity `counts i`. The conclusion supplies an actual composition
   series of `A` of length `∑ i, lengths i` with multiplicity
   `∑ i, counts i`. The original filtration need not have simple factors.
2. `JordanHolderFiltrationDecompositionStatement` takes an ambient
   length witness `HasCompositionSeriesLength A N` and an ambient count
   witness `HasJordanHolderMultiplicity A τ M`. For every supplied finite
   invariant filtration, it supplies functions `lengths` and `counts`
   and actual composition series of all graded pieces realizing both
   functions. Their lengths sum to `N` and their counts sum to `M`.
   The two ambient witnesses need not use the same series.
3. `JordanHolderShortExactAdditivityStatement` takes actual intertwiners
   `i : A.ρ.IntertwiningMap B.ρ` and
   `q : B.ρ.IntertwiningMap C.ρ`, injectivity of `i`, surjectivity of `q`,
   and `LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap`.
   Supplied outer multiplicities `mA` and `mC` imply the actual middle
   multiplicity `mA + mC`, including existence of a middle series.
4. `JordanHolderShortExactDecompositionStatement` uses the same actual
   short exact sequence. A supplied middle multiplicity `mB` yields
   outer multiplicities `mA` and `mC`, each with an actual series witness,
   such that `mA + mC = mB`. No separate outer finite-length premise is
   required in this direction.
5. `JordanHolderInjectiveMonotonicityStatement` says that an actual
   injective intertwiner `A → B`, together with supplied counts for
   both representations, implies `mA ≤ mB`.
6. `JordanHolderSurjectiveMonotonicityStatement` says that an actual
   surjective intertwiner `A → B`, together with supplied counts for
   both representations, implies `mB ≤ mA`.
7. `JordanHolderProductAdditivityStatement` says that supplied counts
   for `A` and `B` give count `mA + mB` for
   `Rep.of (A.ρ.prod B.ρ)`. This is the actual binary product carrier
   with componentwise action, in universe `max uA uB`. It is the finite
   direct sum of two representations, rather than a tensor product.

The filtration statements include `n = 0`, repeated invariant subspaces,
and zero graded pieces. A zero graded piece can have a length-zero
composition series. No strictness or nonzero condition is placed on the
original filtration. Only the refining series in each premise or
conclusion must have simple, hence nonzero, factors.

## Provenance and intended proof

The statements isolate algebraic Jordan–Hölder calculus for modules over
the monoid algebra. They are broader than the original representation-
theoretic applications and are not attributed verbatim to a source.

Silberger, *The Langlands quotient theorem for p-adic groups*, Math. Ann.
236 (1978), printed pp.100–101, motivates the interface. The proof of
Lemma 5.3 compares constituentwise multiplicity bounds by summing over
the factors of a particular inner induction. The proof of Lemma 5.5 uses
two quotient representations and Jacquet exactness to force a strict
multiplicity increase. The present module states only the underlying
algebraic sums and inequalities, for actual finite series and exact maps.
It states no property of induction or Jacquet functors.

The retained original is
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
source ID
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA-256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Printed pp.99–101 (PDF pages 5–7) were read for this contribution;
the multiplicity formulas on pp.100–101 were checked in page images.
No source-specific erratum file is present in the supplied notes.
The published scope audit
`notes/jacquet/silberger-lemma53-scope.md` was also read. That audit is
neither an author erratum nor a Lean theorem. Its constituent restriction
is preserved: no unrestricted Lemma 5.3 or Corollary 5.4 is asserted or used
here.

A later proof can refine each interval of a supplied finite filtration
by lifting and concatenating the supplied graded series. Counting the
concatenated factor indices gives the first claim. Restriction and quotient
of a finite composition series give the converse decomposition, with zero
steps removed. The published series-comparison and multiplicity-independence
theorems identify lengths and counts coming from different supplied series.
The two-step image/kernel filtration and the actual first-isomorphism
equivalences give the short exact sequence claims. Applying them to an
injection or a surjection gives the inequalities. The canonical inclusion
and projection of the actual binary product give its sum formula.
This is a proof plan for a separate proof contribution.

The existing
`Langlands.jordanHolderMultiplicityIndependence` and
`Langlands.HasJordanHolderMultiplicity.unique` in
`Langlands.Representation.Filtration.MultiplicityIndependenceProof`
are available for that later proof; the present definitions do not
restate their claims or assume additivity as a premise.

These statements do not assert finite length of parabolic induction or
Jacquet modules, second adjointness, cuspidal multiplicity formulas,
continuation in parameters, existence of a Langlands quotient, or recovery
of a tempered representation. Those remain separate obligations of the
intended comparison, head, and supported-recovery consumers.
