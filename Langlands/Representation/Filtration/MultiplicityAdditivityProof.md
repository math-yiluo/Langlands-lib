# Additive Jordan–Hölder multiplicities for actual finite series

Author: Worker 430.
Provenance: internal algebraic proof of the existing statement.

`Langlands.jordanHolderMultiplicityAdditivity` proves exactly
`Langlands.JordanHolderMultiplicityAdditivityStatement` from
`Langlands.Representation.Filtration.MultiplicityAdditivityStatement`.
It retains all six independent universes `uK`, `uG`, `uA`, `uB`, `uC`,
and `uT`, over any field and monoid. The theorem is the conjunction
of the seven component theorems described below.

The target pair and its imports are used unchanged. Every asserted
multiplicity still supplies an actual finite composition series.
The proof introduces no total multiplicity function and assumes no
representation-theoretic finite-length or comparison theorem.

## Construction along a finite filtration

`jordanHolderFiltrationAdditivity` first chooses the supplied actual
composition series of each graded representation. The published
`actualQuotientSeriesLift` pulls each series back to a chain of covering
steps between the corresponding two invariant subspaces.
`GradedRefinementProof.assemble` concatenates those interval chains.
It gives an actual ambient composition series, together with a bijection
from its factor indices to all factor indices of all interval chains.
Composing with the lifting bijections gives an equivalence
from `Fin m` to `Σ i, Fin (lengths i)` and an actual representation
equivalence at each matched factor.

Taking cardinalities proves `m = ∑ i, lengths i`.
Restricting the same index equivalence to factors equivalent to the
specified representation `τ` preserves the count. The auxiliary
`card_selected_sigma` explicitly identifies that selected subtype with
the dependent disjoint union of the selected subtypes in each fiber.
`Nat.card_sigma` then gives the sum of the prescribed counts.

This construction includes a filtration with no steps: its concatenated
covering chain has length zero. Repeated original steps and zero graded
pieces are also allowed; their supplied length-zero series simply
contribute empty fibers. No strictness is imposed on the original
filtration, and irreducibility of `τ` is not assumed.

## Decomposition along a finite filtration

`jordanHolderFiltrationDecomposition` uses
`repLength_eq_of_hasSimpleFactors` to identify the supplied ambient
series length with the actual module length of the representation over
the monoid algebra. By `repLength_eq_sum_of_filtration`, the length of
each graded piece is bounded by that finite ambient length. Therefore
each graded piece is a finite-length module.

Mathlib's `isFiniteLength_iff_exists_compositionSeries` supplies a module
composition series of each piece.
`LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`
converts it to an actual representation composition series; the helper
`exists_series` packages this conversion. Define the counts to be the
actual counts of these supplied series and apply the preceding
construction. The length of its ambient series equals the prescribed
ambient length by `repLength_eq_of_hasSimpleFactors`.
`HasJordanHolderMultiplicity.unique` identifies the reconstructed
ambient count with the separately supplied ambient count.
Thus the initial length witness and count witness may use different
series, as the target requires.

## Actual short exact sequences

The existing `Langlands.LengthTwo.twoStep` constructs the actual chain
`0 ≤ S ≤ B`. For an injective intertwiner
`i : A → B` and a surjective intertwiner `q : B → C` with
`range i = ker q`, take `S = i.range`.

The helper `source_equiv_range` restricts `i` to its actual range
and proves bijectivity, giving an actual representation equivalence.
`quotient_equiv_of_surjective` descends a supplied surjective intertwiner
on the upper invariant subspace when its kernel is exactly the lower
subspace; the descended map is bijective and intertwines the actions.
It gives the equivalence from the first graded piece to `A`, by
quotienting the range by zero, and from the second graded piece to `C`,
by descending `q` from the full upper subspace. These are packaged
in `two_step_equivs`.

`jordanHolderShortExactAdditivity` transports the two supplied outer
series and counts through these actual equivalences using
`equivJordanHolderMultiplicityTransport`. Applying filtration
additivity to the two-step filtration constructs the middle series
with count `mA + mC`.

`jordanHolderShortExactDecomposition` takes the actual length from
the supplied middle count witness. Filtration decomposition gives
actual series and counts of its two graded pieces. Transporting through
the same equivalences supplies the two outer count witnesses, and
the two-term sum is the supplied middle count. No finite-series
premise for either outer representation is added.

## Monotonicity and the binary product

`jordanHolderInjectiveMonotonicity` completes an injection to the actual
short exact sequence with quotient by its range. Short exact
decomposition provides the source count and quotient count.
Multiplicity uniqueness identifies the former with the supplied
source count, so it is at most the supplied middle count.

`jordanHolderSurjectiveMonotonicity` uses the actual kernel inclusion
and the given surjection. Decomposition and multiplicity uniqueness
identify the target count as one summand of the supplied source count.

`jordanHolderProductAdditivity` uses Mathlib's actual left inclusion
and second projection of `A.ρ.prod B.ρ`. They are injective and
surjective respectively, and their range and kernel agree.
Short exact additivity gives the count `mA + mB` in the actual
binary product, whose carrier lies in `max uA uB`.

## Provenance and scope

The proof is ordinary Jordan–Hölder calculus for modules over a monoid
algebra, expressed through the existing actual representation objects.
Its route uses the published interval-lifting, graded-assembly,
representation-length, series-transport, and multiplicity-independence
results. It uses the original-source attribution only through the
unchanged statement's explanation that Silberger's constituentwise sums
motivate this broader internal algebraic interface. The proof does not
assert or use unrestricted Silberger Lemma 5.3 or Corollary 5.4.

It proves no property of induction or Jacquet functors, second
adjointness, analytic continuation, tempered representations, or
Langlands quotients. In particular it supplies an algebraic prerequisite
for the recovery and head arguments, and it does not prove those
arguments. Independent review and publication remain separate from
development compilation.
