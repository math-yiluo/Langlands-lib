# Finite-presentation atlases of algebraic-space fibre products

This module establishes the two required properties of the actual
`fibreProduct f g` over an affine scheme `S`. The three spaces are
quasi-separated and have `HasAtlasProperty (LocallyOfFinitePresentation ⊓ QuasiCompact)`.
No property of either morphism is assumed. The existing definitions remain unchanged.

The common-chart construction chooses affine étale surjective scheme atlases
`U → X`, `V → Y`, `C → Z`, locally of finite presentation over `S`. Representability
of maps from schemes to `Z` provides schemes `A = C ×_Z U` and `B = C ×_Z V`.
Their projections to `U` and `V` are étale. Form the actual scheme fibre product
`R = A ×_C B`. The categorical `TripleChartPullback` lemma identifies its map
to `U ×_Z V` as the base change of `C → Z`. It is therefore étale and surjective;
composing with the atlas of the arbitrary fibre-product construction gives the
actual atlas `R → fibreProduct f g`.

Étaleness of `A → U` and `B → V` makes `A` and `B` locally finitely presented
over `S`. The existing scheme cancellation result
`Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp` makes `B → C`
locally finitely presented, since `C` is locally of finite type over `S`.
Base change and composition then give local finite presentation of `R → S`.

Quasi-separatedness of `Z` says precisely that every represented scheme pullback
of its diagonal has quasi-compact projection. Applied to the pairings of
`C ×_Z U` and `C ×_Z V` into the affine products `C ×_S U` and `C ×_S V`, it
makes `A` and `B` compact. The map `B → C` is quasi-compact since `B` is compact
and `C` is affine. Base change and composition give quasi-compactness of `R → S`.
Thus this very atlas witnesses the unchanged finite-presentation atlas predicate.
The previously constructed quasi-separatedness theorem supplies the other conjunct.

`FibreProduct.hasAtlasProperty_finitePresentation` constructs the atlas witness;
it only needs quasi-separatedness of the target. `FibreProduct.finitePresentation`
adds quasi-separatedness of the two sources and proves the exact pair of
properties requested for the constructed space. The corresponding theorem
`FibreProduct.finitePresentation_pullback` transports this pair to the categorical
chosen `Limits.pullback f g` using its canonical isomorphism.

The source correspondence is with Stacks Project, Morphisms of Algebraic Spaces
(version ed88ff78), Lemmas 28.2–28.4 and 28.9 (Tags 03XQ, 03XR, 0410, 05WT),
printed pp.56–58: local finite presentation is checked on actual étale charts,
is stable under composition and base change, and cancels a locally finite type
target structure map. The implementation performs those operations on the
explicit scheme `R`, using the existing scheme theorem for cancellation.
Quasi-compactness is proved on this same atlas via the diagonal pairing as in
Lemma 4.5(4) (Tag 03KN), printed p.5, and the compactness criterion behind
Lemma 8.10 (Tag 073B), printed pp.14–15. The project predicate here is exactly
the existential atlas condition together with the separate quasi-compact
diagonal condition, rather than a new definition of finite presentation.

`TripleChartPullback` is internal categorical infrastructure derived solely from
the four displayed pullback universal properties. This file adds explicit
scheme-atlas refinements to the published construction and proves their
finiteness; no external theorem is assumed as an axiom. Every assertion retains
the arbitrary universe `u`. There is no unproved closure condition or proof
successor left by this unit.

The local instances have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and local
instance scope are unchanged.
