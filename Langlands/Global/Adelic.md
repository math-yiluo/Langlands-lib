# Concrete adeles, ideles, and local maps

Author: Worker 2.

For a number field `K : Type u`, with Mathlib's `Field` and `NumberField`
instances, `Langlands.Global` uses the actual ring of integers, its nonzero
prime ideals, and the associated adic completions. Infinite places and their
completions are Mathlib's archimedean places. All aliases preserve the existing
arithmetic operations and topology definitionally. No topology on the global
field `K` is assumed.

`FiniteAdeles K` is the restricted product over the finite places, relative to
the valuation subrings. Its topology is the final topology of the products
which allow nonintegral coordinates in only a fixed finite set. `Adeles K`
is the product of the archimedean adele ring and this finite adele ring.
`FiniteIdeles K` and `Ideles K` are units with the topology induced by simultaneous
value and inverse coordinates. In particular, the idele topology is not
implicitly replaced by the subspace topology of the adele ring.
`IdeleClasses K` is the actual quotient by the range of the diagonal `Kˣ`
homomorphism and carries the quotient topology.

`finiteProjection` and `infiniteProjection` are ring homomorphisms onto the
corresponding completion. Their continuous units maps are
`finiteIdeleProjection` and `infiniteIdeleProjection`.
`finiteIdeleInclusion` and `infiniteIdeleInclusion` put a local unit in one
coordinate and put `1` in all the others. They are multiplicative inclusions;
the underlying completion-to-adele maps are not additive ring inclusions.
Composing with `ideleClassMap` gives the continuous local maps to idele classes.
`ideleProductEquiv` is a topological group equivalence between full ideles and
the product of infinite and finite ideles. It supplies the inclusions of each
whole factor.

The intrinsic proofs establish continuity and the projection/inclusion
identities. For the finite single-coordinate map, the proof factors through
the restricted-product stage indexed by the complement of the chosen place.
That stage has the ordinary product/subspace topology and its inclusion into
the finite adele ring is continuous. The units-map construction then supplies
continuity with the correct idele topology. The quotient calculation uses the
actual range witness for a principal idele.

## Original sources and correspondence

André Weil, *Basic Number Theory*, second edition, Springer, 1973:

- Chapter IV, §1, pp.59–60, Definition 1 and its preceding construction:
  restricted-product adeles, topology, coordinate projections and diagonal map.
- Chapter IV, §3, p.71, Definition 2: units with the topology determined by
  `x ↦ (x,x⁻¹)`. Proposition 2 and its corollary, p.72, identify the restricted
  product description of ideles.
- Chapter VII, §4, p.118: idele-class quotient and local restrictions.

Retained source: `C:/Central-Library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`.
Literature ID `weil-1973-basic-number-theory`; SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
Printed page `p` is PDF page `p + 17`. Worker 2 read the cited pages directly.

The source describes all places in one restricted product. Mathlib separates
the finite set of infinite places as the first product factor. These are the
same coordinate construction; the split is explicit in the aliases and maps.
The source's principal ideles are represented as a range subgroup rather than
silently identifying `Kˣ` with its image. The continuous quotient map does not
require a separate arbitrary choice of representative.

Pinned Mathlib dependencies: `NumberTheory/NumberField/AdeleRing`,
`NumberTheory/NumberField/InfiniteAdeleRing`,
`RingTheory/DedekindDomain/FiniteAdeleRing`,
`Topology/Algebra/RestrictedProduct/{Basic,TopologicalSpace,Units}`,
and the topological units and quotient interfaces. The elementary bundling and
map proofs here are derived constructions, not separately cited results from
Weil. This group does not assert class field theory, a global Weil group,
compactness of the norm-one idele classes, or existence of prescribed characters.
