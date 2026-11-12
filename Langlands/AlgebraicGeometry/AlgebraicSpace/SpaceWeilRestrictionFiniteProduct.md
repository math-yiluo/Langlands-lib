# Full-test finite-product decomposition of Weil restriction

This internal construction supplies a structural comparison needed to
decompose completed tensor algebras in the adelic Weil restriction argument.
It uses `FiniteProductSections.equiv`, the published iterated-pullback
comparison for finite product bases, and the actual definitions of Weil
restriction and algebraic-space base change.

Let `A` be a commutative ring, let `B i` be a finite family of commutative
`A`-algebras, and let `X` be an algebraic space over `Spec (∏ B i)`.
The factor space is its ordinary base change to `Spec (B i)` along the
original ring projection. `productPresheaf` is the dependent product of
the Weil restriction presheaves of these factor spaces from `B i` to `A`.
Its restrictions act componentwise.

For every scheme `T` over `Spec A`, first split the sections of `X` on
`T ×_(Spec A) Spec (∏ B i)` into its factor tests. The canonical
iterated-pullback isomorphism identifies each factor test with
`T ×_(Spec A) Spec (B i)`. This constructs `sectionsEquiv`.
Its forward component is exactly pullback by `testMap`, which uses
the inverse iterated-pullback comparison followed by the ordinary first
pullback projection to the original product-base test.

The naturality of `testMap` follows from the naturality of the
iterated-pullback comparison and of the factor inclusions.
`ringWeilRestrictionFiniteProductPresheafIso` applies the contravariant
presheaf to this equality, giving a natural isomorphism on all test
schemes. Its component formula states the original test restriction
explicitly.

No factor Weil restriction or product is assumed to be represented by a
scheme or algebraic space. No finite type, separatedness, field,
completeness, or topology hypothesis is used. This unit proves the
full-presheaf decomposition; the geometric representability and the
topological finite-product comparisons remain separate obligations.
