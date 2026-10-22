# Finite-to-absolute degree-two inflation and restriction

Author: Worker 80.

`AbsoluteH2InflationExactness` states the exact sequence

`0 → H²(E/K) → H²(K) → H²(E)`

for a characteristic-zero field `K` and a finite Galois intermediate field
`E` of its algebraic closure. The first map is the existing
`closureInflation K E 2`. The second is the existing
`absoluteRestriction K E 2`, for the specified `K`-compatible embedding of
algebraic closures. Exactness means that inflation is injective and its
additive range equals the additive kernel of restriction. The statement
does not assert surjectivity of restriction.

The relative group is ordinary cohomology of `Gal(E/K)` acting on `Eˣ`.
The two absolute groups are continuous cohomology of the respective
absolute Galois groups acting on their algebraic-closure units, with
discrete coefficient topology. All groups and maps are imported unchanged.
In particular, `closureInflation` first uses the proved inverse of the
finite continuous-to-ordinary comparison, then the actual continuous
inflation. Absolute restriction uses the induced homomorphism of absolute
Galois groups and inclusion of closure units.

The additional algebra instance specifies the embedding
`AlgebraicClosure K → AlgebraicClosure E`. The scalar-tower instance
requires compatibility over `K`, as in the existing absolute restriction
map. No separate agreement with the canonical embedding
`E → AlgebraicClosure E` is imposed. In particular, an inferred tower
`E → AlgebraicClosure K → AlgebraicClosure E` would use the `E` action
inherited through the supplied closure embedding; that tower is automatic
and would not express canonical-embedding compatibility.

The assertion therefore ranges over every `K`-compatible closure embedding.
These are data specifying the map, not a cohomological vanishing or
exactness premise. Characteristic zero ensures that the algebraic closures
used here are separable closures. The result is stated in an arbitrary
common universe `u`. This prerequisite does not assert the host theorem's
independent-universe extension case.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer, 1979, Chapter X, section 4, Corollary to Proposition 6,
printed page 156 / PDF page 162. The registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
is retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 80 read PDF pages 160–162, including the continuous-cohomology
convention, Proposition 5, Proposition 6 and its corollary. No current
project errata entry for this source was present when checked.

Serre's base field `k` is Lean's `K`, and his extension `K` is Lean's `E`.
His groups `B_k` and `B_K` are defined as degree-two absolute Galois
cohomology, so they are precisely the mathematical groups called `H²(K)`
and `H²(E)` above. The finite-dimensional and characteristic-zero
restrictions specialize the source. Section 3 explains the equivalence
between the direct-limit and continuous-cochain descriptions; section 4
describes the maps using base-field-compatible field embeddings.
Proposition 5 establishes independence of the chosen base-field-compatible
embedding. Together with the corollary, this supports exactness for every
`K`-compatible closure embedding, including choices that need not agree
with the canonical embedding of `E` into its own closure. A proof of this
statement must justify that independence for the project's actual maps,
as well as the passage to its continuous-cohomology model.

The source derives the corollary by passing the finite-tower exact
sequence to the limit. This file only defines the proposition target.
It provides neither a proof of that passage nor any invariant map to
the rationals modulo the integers, restriction-degree normalization,
or local invariant-existence theorem.
