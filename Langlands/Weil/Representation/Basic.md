# Finite-dimensional representations and genuine isomorphism classes

Worker 17 implements a reusable algebraic layer for Weil parameters using
Mathlib's `Rep` and its full-subcategory interface. `Langlands.FiniteRepresentation`
has a field of coefficients, a monoid, and an independent universe for its actual
carrier vector spaces. Its objects have finite-dimensional carriers. Rank zero
is permitted so that later kernels and sums have a natural ambient category.
There is no built-in topology, irreducibility or semisimplicity restriction.

`of` retains the supplied carrier and action. The category and its identity and
composition laws are inherited from the full subcategory of `Rep`. `homEquiv`
identifies its morphisms with Mathlib linear intertwining maps. `Equiv` is
Mathlib's representation equivalence, including an actual inverse linear map,
and also permits different source and target carrier universes. `isoOfEquiv`
and `equivOfIso` connect that interface to categorical isomorphisms.

`IsIsomorphic` means that a representation equivalence exists.
`isomorphismSetoid` supplies reflexivity, symmetry and transitivity through the
identity, inverse and composition of those equivalences. `IsomorphismClasses`
is the resulting quotient. `classOf_eq_iff` states its exact equality criterion.
The dimension equality for a linear equivalence proves that `classRank` is
well-defined. `IsomorphismClassesOfRank n` is the subtype of classes of rank `n`;
it supports every positive natural rank and also zero. The quotient is relative
to a fixed carrier universe; cross-universe equivalences are available at the
object level, without asserting equality of quotients in different universes.

`propertyIsomorphismSetoid` restricts that same genuine relation to a subtype
defined by any explicit predicate. `IsomorphismClassesWith` and
`IsomorphismClassesOfRankWith` therefore support separate continuous,
irreducible, or semisimple parameter sets. `forgetPropertyClass` descends the
forgetful map to the unrestricted quotient. These constructions need no
unproved assertion that a predicate is invariant under isomorphism: their
representatives are already required to satisfy it, and their equivalence
relation is the restriction of the proved relation on all representations.

This is a generic algebraic infrastructure construction. Complex Weil
representations will use this category together with separately stated topology
and inertia conditions. It does not construct a local Weil group or identify
continuity conditions, and it does not define a Langlands correspondence.

## Source correspondence

John Tate, *Number theoretic background*, in *Automorphic Forms,
Representations and L-Functions*, Part II (1979), section 2, printed page 9
(PDF page 18), defines finite-dimensional complex representations on vector
spaces and their isomorphism classes. His continuous Weil representations add
a condition that is deliberately deferred to the next module here. The
implementation generalizes the algebraic layer to any field and monoid and
makes the isomorphism relation and its quotient obligations explicit.

- Literature ID: `tate-1979-number-theoretic-background`.
- Retained source: the Corvallis publication folder's `Part II.pdf`.
- SHA-256: `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- Pinned Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- Mathlib interfaces: `RepresentationTheory/Rep/Basic.lean`,
  `RepresentationTheory/Intertwining.lean`,
  `CategoryTheory/ObjectProperty/FullSubcategory.lean`, and
  `LinearEquiv.finrank_eq`.

The category, equivalence laws and quotient well-definedness proofs are
intrinsic to these definitions. No classification or continuity-equivalence
theorem is assumed. This pair is development pending independent review.
