# Local trivialization of the constructed associated sheaf

Author: Worker 57. This is a proposition target, not a proof.

`EtaleAssociatedTrivializationStatement` says that a finite geometric etale
torsor trivializes the actual invariant sheaf constructed in
`Coefficients.Associated` and `Coefficients.Etale`. It quantifies every scheme
`X`, group `G`, actual action on an etale object `Y`, and commutative ring `R`
in universe `u`. The torsor predicate requires finite `G`, a finite surjective
etale cover, and unique transport between any two lifts of each geometric
point. It does not contain a sheaf or a trivialization isomorphism.

The conclusion is existence of a natural isomorphism of two functors from
the category of `R`-module representations of `G` to sheaves on the
localization of the actual small etale site at `Y`. The left functor forms
the invariant associated sheaf, then restricts it to that localized site.
The right functor forgets the representation action, forms the ordinary
constant coefficient sheaf on `X`, and restricts it to the same site.
Thus the conclusion asserts simultaneous trivialization compatible with
every equivariant coefficient map, including the reduction maps of an
integral coefficient system. No particular trivialization or output local
system is an input. No chosen constructor is exported before this theorem
is proved.

The displayed localization uses Mathlib's `overPullback`, namely restriction
to objects with a morphism to the given etale cover. The target uses the
restriction of the base constant sheaf on its right-hand side; it does not
silently identify independent sheafification choices by definitional equality.
No comparison with adic completion, derived limits or cohomology is asserted.

This is a derived general theorem obligation for Harris (1999), Section 4,
printed page 311 (PDF page 13), the finite coefficient descent and inverse
system preceding Proposition 4.10. That original passage was read by Worker 57.
The explicit functorial form isolates the required descent result from
Harris's later cohomological comparisons. It is more general in coefficients
and base schemes than the application. It still requires an actual finite
etale torsor. It does not construct Harris's scheme models, prove the torsor
condition for those levels, or assert the whole Harris theorem.

Source: `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
*Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), pp.299-318;
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
Formal dependencies are `Langlands.Shimura.Coefficients.Associated` and
`Langlands.Shimura.Coefficients.Etale` (`etaleAssociatedFunctor`,
`IsFiniteGeometricTorsor`), and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.

A proof must establish this entire declaration with all its quantifiers.
The expected argument: the torsor condition makes the action map
`G × Y → Y ×_X Y` a bijection on separably closed points between etale
`Y`-schemes, hence an isomorphism; over `Y` the product with the cover is
therefore `G` copies of the base, and the invariants of `G` copies of a
constant sheaf under the diagonal action are one copy, compatibly with
equivariant coefficient maps. This sketch is not formalized here.
