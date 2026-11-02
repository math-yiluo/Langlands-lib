# The actual affine unit comparison

This internal result supplies bijectivity of the published `candidateMap b` on
all affine scheme tests over `Spec k`. It derives the geometric comparison from
the existing determinant-open construction and `algebraicPointEquiv`; it does
not assume representability.

`affineTest k B` is `Spec B` with the specified algebra structure. The equivalence
`affineHomEquiv` identifies its morphisms to the unchanged candidate with
`k`-algebra homomorphisms from `candidateRing b`. The inverse is `affineMorphism`.
The canonical affine pullback isomorphism supplies `affineFibreCoordinates`,
identifying actual fibre-product global functions with `B ⊗[k] A`.

`affineFibreMap` compares the induced morphism of actual fibre products with
the spectrum of the tensor map. Its proof compares both pullback projections:
the first uses naturality of `relativeProjection`, and the second uses
`relativeSpace_map_snd`. The affine tensor inclusions give equality of the
resulting ring maps. Applying global functions and the naturality of
`Scheme.ΓSpecIso` proves `affineFibreCoordinates_naturality`.

`candidateMap_affine_coordinates` applies that identity to the actual universal
unit, using its published coordinate formula. Consequently the actual
comparison is the algebraic-unit equivalence after the two coordinate
equivalences. Injectivity and surjectivity give
`candidateMap_affineTest_bijective`.

For an arbitrary affine `T` over the base, pull its structure map across
`T.left.isoSpec` and take `Spec.preimage` to obtain the algebra structure on its
global-functions ring. This defines an isomorphism in the over category from
`T` to the corresponding `affineTest`. Naturality of the same candidate map
transports bijectivity across that isomorphism, proving
`candidateMap_affine_bijective`.

The universe parameter is arbitrary. No nontriviality, positive-rank,
reducedness, separability, or additional finiteness hypotheses are imposed.
The remaining extension from affine tests to arbitrary schemes requires
restriction and gluing; this module makes no arbitrary-scheme representability
claim.
