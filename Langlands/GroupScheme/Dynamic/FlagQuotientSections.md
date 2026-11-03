# Transport of algebraic sections of actual flag-quotient maps

Author: Worker 1275.

This internal derived construction transports an actual relative-scheme section
along a compatible morphism of the source and an automorphism of the quotient.
It does not establish quotient representability, a quotient action, properness,
a big cell, or rational-point surjectivity.

For an existing map `π : X ⟶ Q`, source endomorphism `f`, quotient isomorphism
`e`, and section `s` on an open `U`, the construction uses the actual open
`e.inv.left ⁻¹ᵁ U`. The morphism `restrictedOver k e.inv U` maps that open
subscheme into `U`; composing it with `s` and then `f` defines
`translatedFlagSection`. If `f ≫ π = π ≫ e.hom`, associativity, the original
section equation, the restriction square and `e.inv_hom_id` prove its section
equation. If `q ≫ e.hom = p` and the image of `q` is contained in `U`, applying
`e.inv` shows that the entire image of `p` lies in the translated open.
Consequently a section near `q` gives sections near all rational points when
compatible lifts of transitive quotient automorphisms are supplied explicitly.

`rationalLeftTranslation` is the actual relative-scheme isomorphism given by
left multiplication by an identity-test rational group point. Its inverse is
left multiplication by the inverse point; its composition law follows from the
group structure on every test-scheme Hom set and naturality of multiplication.

Provenance: elementary relative-scheme restriction, group-object and category
laws in the current Library and pinned Mathlib. All geometric premises are
explicit. This helper is conditional and does not prove the full published
`DynamicFlagQuotientExistenceStatement`.
