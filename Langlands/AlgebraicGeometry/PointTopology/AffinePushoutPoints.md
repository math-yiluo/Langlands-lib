# Actual points of arbitrary algebra pushouts

Author: Worker 105.

This is derived algebra-point infrastructure for Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 2.1 and its proof, printed pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For any span C → A,B in the actual category of commutative R-algebras and
any cocone c, `affinePushoutPointComparison` restricts an actual point of
the cocone vertex to the two factors. The cocone equation makes the pair
compatible over C.

For a colimit cocone, `affinePushoutPointHomeomorph` constructs a
homeomorphism from the vertex's evaluation point topology to the
compatible-pair subspace of the product of the factor evaluation point
spaces. It first gives A and B their C-algebra structures from the span
maps. The constructed tensor pushout and c are isomorphic by their
proved colimit universal properties. Reindexing evaluations by the
resulting R-algebra equivalence and then using the constructed tensor
compatible-pair homeomorphism gives a homeomorphism. The colimit
factorization equations prove that its map is the actual restriction
comparison. The final application lemma records that precise map.

The coordinate algebras and R lie in one arbitrary universe, and S may
lie in an independent universe. In particular, the proof does not use
the cocone's colimit universal property with S as a category object.
Only S is topological, with continuous ring operations. No finite
generation, fixed C-algebra structure on S, Hausdorffness or locality
is required.

The unit is a derived generalization of the algebraic form of the
source fibre-product comparison. Actual scheme points, the complete
axiomatic characterization, and nonaffine gluing remain separate.
