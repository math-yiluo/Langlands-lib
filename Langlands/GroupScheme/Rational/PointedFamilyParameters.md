# Separating the initial variable from universal commutator parameters

This internal construction regroups the published
`PointedCommutatorFamily.source G V n` as
`V ⊗ PointedCommutatorFamily.parameters G n`.
The isomorphism `sourceProductIso` uses the inverse right unitor at index
zero and then the product associator at each successor.

`basepointSection_sourceProductIso` proves that the published whole
basepoint section becomes exactly the map that sets the initial variable
to its basepoint and retains the identity on the entire parameter scheme.
The proof is induction using Cartesian product projections. No geometry,
field, rational-density, or unipotence premise occurs in this identity.

The construction is derived from the actual product universal properties;
it does not invoke an external structure theorem.

`family_eq_one_of_basepointSection` applies this identity to an actual
relative scheme morphism from the nested source beginning with the affine
line. It assumes a field, reducedness and dense actual rational points of
that source, a separated target group, affine-line constancy for that
target, and identity of the restriction to the whole basepoint section.
It concludes that the entire family is the group identity.

The proof transports reducedness and density through `sourceProductIso`,
using reducedness under an open immersion and the published density
transport lemma. The basepoint identity becomes the whole zero-section
identity required by `HasConstantAffineLineMaps.family_eq_one_of_zeroSection`.
Precomposition with the inverse isomorphism and cancellation return the
result to the original nested source.

This unit does not prove rational-point density, a separable base-change
comparison, the vector-factor decomposition, or the full all-field
woundness criterion. Its density and reducedness hypotheses remain
explicit.
