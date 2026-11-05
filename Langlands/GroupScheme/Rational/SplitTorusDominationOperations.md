# Operations on pointed split-torus domination

This internal derived unit provides operations needed in the structural reduction
of the unipotent splitness criterion. It does not establish that criterion.
All schemes and morphisms use the existing group-scheme interfaces.

Finite products of split tori remain split over an arbitrary base, by induction
on the finite index type using the existing empty-product, binary-product and
reindexing isomorphisms. Consequently, a dominant ordered power of a pointed
morphism from a split torus gives pointed split-torus domination: the actual
group-scheme product maps to the scheme-level finite power, and its section
proves that the composite still has dense range.

Dominant group homomorphisms and group-scheme isomorphisms preserve the supplied
parametrization. Binary products preserve parametrizations when the targets are
affine, reduced and flat over the field. Dominance into a reduced scheme gives schematic
dominance; flat whiskering then makes the product morphism schematically dominant.
The product map carries the identity to the identity by its two projections.

The existing pointed-image-generation theorem supplies a smooth affine
geometrically connected generated representative for a pointed split-torus
image, with a dominant finite ordered power of its canonical factor. Cancelling
the closed inclusion proves that this factor is pointed. The finite-power
construction therefore gives a pointed split-torus parametrization of that
representative.

Schematically dominant precomposition does not change the represented closed
image envelope. One inclusion follows by composing each competing
factorization with the source map. The reverse inclusion follows from descent
of factorization through a closed immersion along a schematically dominant map,
using `GeneratedImage.sourceFactor`. This identifies a representative generated
from the composite parametrization with any representative generated from the
original pointed morphism.

In particular, a pointed morphism from a reduced split-torus-dominated group
into a smooth affine group has a split-torus-dominated generated subgroup.
Applying this to the commutator morphism from the square of a smooth affine
group proves inheritance by its actual scheme-theoretic derived subgroup.
No multiplicativity or boundary extension is imposed on the parametrizations.

The provenance is internal: these are consequences of the published
`Torus.Products`, `Torus.PowerDomination`, `ImageGenerationPointed`,
`ImageGenerationSourceTransport` and `Derived.CommutatorEnvelope` results.
They support the structural proof route described in Springer,
*Linear Algebraic Groups*, second edition, Theorem 14.3.8(i), printed
pp.245–246. The module makes no split-unipotence assertion.

Isomorphism transport reuses the existing
`HasPointedSplitTorusDomination.of_iso` from
[SplitTorusDominationRefinement](SplitTorusDominationRefinement.md).
