# Central coverings of evaluated actual compact intertwiners

This internal derived argument uses the actual finite compact Hom source and
the fixed-vector central-generation result. The target is an arbitrary genuine
complex enveloping module with a compatible whole compact action. An
equivariant map from a finite continuous compact representation has image
stable under the actual compact Lie generators.

A linear map from a finite source lies in the enveloping-generated Hom source
exactly when all its values lie in the original enveloping-generated source.
One implication evaluates sums of enveloping actions. For the other, the
coordinate equivalence between linear maps and tuples is linear over the
enveloping algebra. Single-coordinate insertion carries the generated original
source into the generated Hom source, and the sum of these insertions recovers
the map.

`compactHomCentralEvaluationSpan` is the sum of the full-center orbit spans of
the values of a finite Hom family on a finite basis. Evaluation of every map
in that family's central covering lies in this finite evaluation covering:
expand the argument in the finite basis, commute its complex coordinates with
the enveloping action, and use closure of the target submodule.

The invariants of the conjugation Hom action are the actual intertwiners.
Applying the fixed-vector covering to the finite Hom source and then evaluating
gives `exists_finite_central_cover_of_intertwiner_values`. One finite family
works for every intertwiner whose values lie in the generated original source.
No irreducibility, injectivity of the source map or topology on the target is
assumed. Universes and all natural ranks are retained.

If the finite source generates the entire target, the companion theorem
`exists_finite_central_cover_of_generated_isotypic` covers its algebraic
isotypic span, the sum of all intertwiner ranges, by that same finite family.
This corollary needs no irreducibility of the selected compact representation.

This unit does not yet compare an ambient isotypic intersection with the
isotypic part of the actual generated module, construct that module's finite
compact source, or prove the compact-type central-span statement or automorphic
differential growth theorem.
