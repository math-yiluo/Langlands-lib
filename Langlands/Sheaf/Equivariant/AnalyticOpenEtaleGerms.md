# Ordinary germs of actual analytic higher direct images

This internal unit uses the actual ordinary direct image `etaleUnderlyingSheaf`
and actual lifted ordinary site points `underlyingTopologyPoint`, with independent
`u`, `v` and `uL` levels and coefficient universe `max u (v + 1) uL`. No geometric
separation, field-point-surjectivity or group-action hypothesis is required.

`eq_of_underlyingTopologyPointGerms_eq` proves ordinary sheaf sections are equal
if their germs at every ordinary point are equal. Equality in the actual point
fiber has a representative on a smaller open neighborhood. These neighborhoods
cover the original open, and the sheaf's separatedness proves equality of its
sections. Applying this to values of two morphisms proves
`underlyingTopologyPointFibers_jointlyFaithful`.

`etaleUnderlyingGermCohomology X R y q` is the existing right-derived-functor
construction applied to actual ordinary direct image followed by its actual
fiber at `y`. The construction uses the proved analytic sheafification and
enough-injectives instances. The fiber is additive and exact: it preserves
finite limits as a site-point fiber and colimits by its actual skyscraper
adjunction. `etaleUnderlyingGermDerivedIso` is the existing exact postcomposition
comparison `LeftExactHomology.derivedNatTrans`, made invertible by that exactness.
It identifies the derived composite with the ordinary point fiber of
`etaleUnderlyingHigherDirectImage` in each degree, naturally in the étale sheaf.

`isZero_etaleUnderlyingHigherDirectImage_iff_germCohomology` gives a precise local
criterion: an ordinary higher direct image is zero if and only if all the
displayed germ cohomology modules are zero. Forward transport uses the actual
fiber and comparison isomorphism. Conversely, the isomorphisms make every point
fiber of that higher direct image zero. Joint faithfulness then identifies its
identity morphism with zero, proving the sheaf is zero.

These are internal sheaf and derived-functor calculations. They assert no
identification of analytic germs with absolute-Galois cohomology, no special
smooth-point-product vanishing, and no equivariant cohomology comparison. Such
analytic local inputs remain separate obligations.
