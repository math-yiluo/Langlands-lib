# Lifting a quotient composition series to a covering chain

Author: Worker 244. Coauthor: Worker 122, who designed this interface for
the graded-refinement proof task `8f135e79-b688-4075-b8e6-b05a81a36883`.
Provenance: internal derived module-theoretic content (see below).

The proposition definition `Langlands.ActualQuotientSeriesLiftStatement` in
`Langlands.Representation.Filtration.IntervalLiftStatement` states one
existence claim. This pair does not prove that claim.

## Statement

The proposition quantifies over the following data:

- a coefficient field `k : Type uK`;
- a monoid `G : Type uG`;
- a representation `A : Rep.{uV} k G`;
- invariant subspaces `S T : Subrepresentation A.ρ`, with the premise
  `S ≤ T`;
- a natural number `n`;
- an actual finite filtration
  `f : ObjectRepFiltration (Rep.of (LengthCriterionProof.quotientRep S T)) n`
  of the successive quotient representation of `T` by `S`.

Its last hypothesis is `f.HasSimpleFactors`: every graded quotient of `f` is
irreducible, so `f` is an actual composition series of the quotient.

The conclusion asserts that there exist

- a relation series
  `c : RelSeries {(X, Y) : Subrepresentation A.ρ × Subrepresentation A.ρ | X ⋖ Y}`
  with `c.head = S` and `c.last = T`;
- an equivalence of index types `e : Fin c.length ≃ Fin n`;

such that for every `i : Fin c.length` there is an actual
`Representation.Equiv` from
`LengthCriterionProof.quotientRep (c i.castSucc) (c i.succ)` to
`(f.gradedRepresentation (e i)).ρ`. Each equivalence is asserted to exist
using `Nonempty`.

In words, `c` is a chain of invariant subspaces of `A` from `S` to `T` in
which each member is covered by the next one in the lattice of invariant
subspaces. The relation is written as the set of pairs `(X, Y)` with `X ⋖ Y`,
since Mathlib's `RelSeries` takes a relation of type `SetRel`. No
`JordanHolderLattice` instance on `Subrepresentation A.ρ` is assumed or used.
The quotient representations on both sides of each equivalence are actual
quotient representations, not labels or isomorphism classes.

## Reading of the conclusion

- The equivalence `e` matches every step of `c` with exactly one factor
  occurrence of `f`. Distinct indices stay distinct even when their factors
  are equivalent, so multiplicities are kept. The bijection forces
  `c.length = n`; no separate equality is stated.
- The statement does not prescribe the order of the matching. A proof that
  takes preimages of the members of `f` would produce the identity matching
  up to the length identification.
- Each step of `c` is a covering step. Through the published lemma
  `LengthCriterionProof.isIrreducible_quotientRep_iff`, this means that each
  step's successive quotient `quotientRep (c i.castSucc) (c i.succ)` is
  irreducible. This agrees with the irreducibility of the matched factor of
  `f`; the statement does not rely on it.

## Scope of the quantifiers

- The quantifiers include `n = 0` and `S = T`. If `S = T`, the quotient
  representation is zero. A filtration with simple factors then has length
  zero, and the conclusion asks for a chain of length zero at `S`.
- `G` is an arbitrary monoid. There is no finite-dimensionality assumption,
  no global finite-length assumption on `A`, and no assumption that `A` has a
  composition series. Only the quotient of `T` by `S` is assumed to have one,
  namely `f`.
- The premise `S ≤ T` is needed. Without it no chain of covering steps can
  start at `S` and end at `T`, while `quotientRep S T` would still be defined.
- The universes `uK`, `uG` and `uV` are independent. Lean inspection of the
  unapplied proposition reports exactly these three level parameters.

## Definitions reused

The sole import is `Langlands.Representation.Filtration.LengthCriterionProof`.
From it the statement uses `LengthCriterionProof.quotientRep S T`, the actual
quotient representation of `T` by its invariant subspace `S ⊓ T` (which is
`S` when `S ≤ T`), carried by `T.toSubmodule ⧸ lower S T`. For a filtration
`s` of an actual representation, the representation of the graded quotient
`s.gradedRepresentation i` is definitionally `quotientRep` of the two
consecutive members of `s`; the published lemma
`LengthCriterionProof.hasSimpleFactors_iff_covBy` uses this agreement.
`ObjectRepFiltration`, `HasSimpleFactors` and `gradedRepresentation` come
unchanged from `Langlands.Representation.Filtration.ObjectDefinitions`.
`Rep.of` is Mathlib's bundling of a representation, so the representation of
`Rep.of (quotientRep S T)` is `quotientRep S T` itself. No existing Library
pair is modified.

## Provenance

This is an internal statement. It is not a verbatim theorem from the
literature, and no source is cited for it. It isolates one step of the
separate proof task `8f135e79-b688-4075-b8e6-b05a81a36883` for the published
statement `Langlands.GradedJordanHolderRefinementStatement`. That proof
refines each graded piece of a filtration by a supplied composition series
and concatenates the results. This statement covers the refinement of one
graded piece only. It does not cover concatenation across a finite
filtration or the final matching of two representations' factors.

The mathematical rationale is the correspondence between invariant subspaces
of the quotient of `T` by `S` and invariant subspaces of `A` between `S` and
`T`. The published `LengthCriterionProof.pull` constructs the preimage in `A`
of an invariant subspace of the quotient. Pulling back the members of `f`
should give a chain from `S` to `T`. For consecutive members `U ≤ U'` of `f`,
the quotient of the preimage of `U'` by the preimage of `U` should be
equivalent to the quotient of `U'` by `U` (the third isomorphism theorem).
That quotient is irreducible, so each step is a covering step. This rationale
is not a Lean proof. The endpoint, order and covering facts and the actual
quotient equivalences are the obligation of a separate proof task, to be
published after this statement.
