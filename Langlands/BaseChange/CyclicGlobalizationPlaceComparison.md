# Completing the split and field tensors of cyclic globalization

A cyclic globalization uses the completed tensor at its prescribed place and at its
split auxiliary places. When the tensor is isomorphic to a field, there is exactly
one place above the lower place. The explicit map to that completion is the
corresponding projection of the Library's completed tensor comparison. It sends
`a ⊗ b` to the product of the two actual scalar embeddings and intertwines
`id ⊗ σ` with the completed automorphism extending `σ`. Both directions are
continuous when the tensor has the lower completion's module topology.

The completion product has a nontrivial idempotent whenever it has two distinct
factors. A field rules this out, and the existence of a place above provides its
unique factor. At a split place the tensor is a product of copies of the lower
completion. Projection onto any actual upper completion is surjective. It sends
some coordinate idempotent of the split product to one, so every value of the
projection is the image of a lower scalar. Each upper completion therefore has
relative degree one. The corresponding scalar embedding and its inverse are
continuous for the original completion topologies.

This is internal support for the field identifications in Arthur–Clozel, Chapter 1,
§6.3 and the proof of Proposition 6.9(ii), using the Library's actual completion
maps and the split cyclic tensor in `CyclicFieldGlobalizationStatement`.
