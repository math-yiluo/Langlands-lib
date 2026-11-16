# Target invariance of étaleness on all recognized pieces

Author: Worker 208.

This internal prerequisite complements the source-invariance results by
proving that postcomposition with a full strong quasi-isomorphism does not
change `IsEtaleAllPieces`. Let `K : Type u` be a complete ultrametric normed
field, with independent space and original index universes `v` and `w`.
For `f : StrongHom A.saturatedPresentation B.saturatedPresentation` and
`g : StrongHom B.saturatedPresentation C.saturatedPresentation`, assume
`hg : g.IsQuasiIso`. There is no separation or compactness assumption.

`IsQuasiIso.comp_preimage_image` uses ambient injectivity of `g` to identify
the composite inverse image of `g(W)` with the inverse image of `W` under
`f`. `comp_preimage_fullRecognitionImage` transports this identity to the
actual recognized image constructed in `QuasiIsoSourceEtale`.

`IsFiniteOver.of_postcomp_quasiIso` starts with a finite composite over
source neighborhood `V` and target neighborhood `U`. The new target
neighborhood is `g.baseMap ⁻¹' U`. For each recognized subset `W` there,
choose its recognized image `Z` under `g`. The composite's finite inverse
image `P` over `Z` has exactly the required locus over `W`, by the preceding
inverse-image identity. The pair-system composition equation identifies
the composite bounded pullback with `f`'s pullback after the bounded image
comparison for `g`. Precomposing with its bounded inverse recovers exactly
`f`'s actual pullback. Composition of finite Banach maps gives finiteness.

`HasAllPiecesAt.of_postcomp_quasiIso` works for every pointwise condition
`Q` which composes along maps of finite type and holds for bounded algebra
equivalences. It retains the original source neighborhood and pulls back
the open target neighborhood along `g`. For any prescribed recognized
piece over `W`, its locus agrees with the finite inverse image over `Z`,
so the actual recognized subsets coincide. The condition on the composite
therefore applies at the same spectrum point. Composing that condition
with the inverse bounded comparison gives `Q` for `f`'s pullback.

The flatness and unramifiedness specializations use the Library's
pointwise composition laws and algebraic finite étaleness of bounded
algebra equivalences. `IsEtaleAtAllPieces.of_postcomp_quasiIso` retains the
same open source neighborhood. Finally,
`isEtaleAllPieces_postcomp_quasiIso_iff` gives the equivalence with
`f.IsEtaleAllPieces`; its reverse direction composes `f` with the already
proved étaleness of the quasi-isomorphism `g`.

This is derived infrastructure from actual recognized-image constructions,
pair-system composition and previously proved affinoid pointwise laws.
It uses no external theorem translation or unproved geometric premise.
Transport through arbitrary localized isomorphisms and cancellation by a
general étale map are separate obligations.
