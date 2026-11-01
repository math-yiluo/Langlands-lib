# Actual induction maps for local triple transfers

This internal contribution supplies actual induction maps needed to reduce
the local repeated-factor transfers to product irreducibility. It does not
prove either local transfer or the required product irreducibility.

`irreducibleTwoFactorSwapIso` considers any two-slot shape and two actual
irreducible smooth factors. The published
`Classification.twoFactorProductConstituentCommutativity` gives matching
actual Jordan–Hölder factors for the products in the two orders.
If the original product is irreducible,
`RepresentationExactComparison.nonempty_equiv_of_sameFactors` gives an
actual representation equivalence. The constructor bundles this as a smooth
isomorphism to the product over the literally permuted shape and family.
It does not claim that a reducible product is isomorphic to its reverse.

`exists_inductionInjection_of_cuspidalOccurrence` starts with an actual
irreducible cuspidal constituent of the Jacquet module of an irreducible
admissible ambient object. Admissibility of that Jacquet module and the
published cuspidal constituent theorem make the constituent a quotient of
the whole Jacquet module. First adjunction turns this surjection into a
nonzero map to its normalized induction. Simplicity of the source makes the
map injective. The induction's irreducibility is not a premise.

`uniformTripleTensor_irreducible_cuspidal` applies the published actual
cuspidal tensor theorem to the three supplied supercuspidals.
`exists_uniformTripleInductionInjection` then specializes the preceding
injection construction to the uniform three-block occurrence.
Conversely, `uniformTripleOccurrence_of_inductionInjection` applies the
published nonzero-induction-map Jacquet quotient theorem: the source is
nonzero, and the tensor target is irreducible, so the Jacquet map is
surjective. The resulting quotient is an actual subquotient. This converse
uses the carrier universe `max uF uV`, matching the existing quotient
interface and the ambient target; the preceding helpers retain independent
unrestricted field and carrier universes.

All functors and character normalizations use the supplied topological data
`T`. The actual injection and quotient maps are retained. In particular, the
initial occurrence remains an actual subquotient; its quotient refinement is
proved using the cuspidal constituent theorem.

The provenance is internal composition of the published interfaces above.
For independence, the two-factor commutativity proof was checked through its
actual annihilator-series, smooth-duality and inverse-transpose argument.
It uses Gelfand–Kazhdan on simple factors, not classification of segments.
Its finite-length input is proved by actual blockwise cuspidal embeddings,
ordered induction in stages, and the lower finite-length theorem for cuspidal
induction. Those embeddings use minimal nonzero Jacquet modules and
admissible cuspidal tensor factorization; they do not assert a global
decomposition by cuspidal lines, ordered quotient coverage or multisegment
exhaustion. The earlier audit of actual Jacquet constituent and tensor proofs
is retained. The import audit records 634 project modules and finds none of
the eight excluded classification conclusions or their proof successors.
