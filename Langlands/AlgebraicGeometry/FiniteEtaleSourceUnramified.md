# Unramifiedness detected by a finite etale source cover

This internal helper works with actual schemes in an arbitrary universe. For
`p : W ⟶ X` and `g : X ⟶ S`, it proves formal unramifiedness of `g` when `p`
is quasi-compact, surjective and etale and `p ≫ g` is etale. The final
corollary specializes to finite etale surjective `p`. No affineness or
Noetherian hypothesis is imposed.

`sourceDiagonalComparison` is the canonical map from `W ×[X] W` to
`W ×[S] W`. Its two projection lemmas state that its composites with the
projections are the projections of `W ×[X] W`.
`sourceDiagonalCover` is the canonical map from `W ×[S] W` to `X ×[S] X`
induced by `p` on both factors.
`sourceDiagonalComparison_isPullback` identifies the comparison as the
base change of the diagonal of `g`; it uses Mathlib's categorical diagonal
pullback square. The `sourceDiagonalComparison_mono` instance follows by
base change of the diagonal's monomorphism.

`sourceDiagonalComparison_etale` observes that the first projection from
`W ×[X] W` is etale, being a base change of `p`. The first projection from
`W ×[S] W` is etale because `p ≫ g` is etale. Mathlib's cancellation of an
unramified postcomposition therefore makes the comparison etale.
`sourceDiagonalCover_fpqc` uses stability under base change and composition
to show that the map on the two factors is surjective, flat and
quasi-compact. Mathlib's `MorphismProperty.pullbackMap` implements this
factorization into two base changes of `p`.

`isOpenImmersion_diagonal_of_surjective_etale_comp` first makes the
comparison an open immersion: it is a flat monomorphism locally of finite
presentation. Descent of open immersions along the preceding fpqc map then
makes the diagonal of `g` an open immersion.
`formallyUnramified_of_surjective_etale_comp` applies Mathlib's implication
from open diagonal to formal unramifiedness.
`formallyUnramified_of_finiteEtale_comp` uses the quasi-compactness of a
finite morphism.

The provenance is a derived diagonal argument supplying the unramified
part of the etale case in the Stacks Project, Lemma 35.14.5, Tag
[05B5](https://stacks.math.columbia.edu/tag/05B5), registered as
`stacks-smooth-etale-source-descent-2026-11-02` (snapshot `05B5.html`).
The source states a more general smoothness and etaleness descent result
and omits the etale proof. This module proves only the stated formal
unramifiedness consequence under an etale quasi-compact cover; it does not
assume the omitted proof or the source-descent statement for smoothness.
The implemented route uses Mathlib's fpqc descent of open immersions and
its theorem on flat monomorphisms locally of finite presentation.
