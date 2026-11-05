# Rank-one promotion from ordinary adic pullbacks

For a universally closed morphism from a locally noetherian actual scheme `X`
to the spectrum of a local commutative ring `R`, and a finitely presented
actual module sheaf `M`, `lineBundleOfAdicPullbacks` constructs a line bundle
whose underlying module is exactly `M`, provided every ordinary pullback to
the actual thickening `X ×[Spec R] Spec (R/m^(n+1))` is locally free of rank one.
Here `m` is the maximal ideal of `R`. The arbitrary universe `u` is retained.

A closed-fibre point lifts to every thickening because the base quotient's
spectrum has image the vanishing locus of `m^(n+1)`, which contains the closed
point, and the scheme pullback has points over every compatible pair.
The zeroth thickening stalk is nonzero, so its stalk-map kernel is proper.
The actual adic kernel formula identifies that kernel with the extension of
`m` in the ambient stalk.

At every thickening point, `adicQuotientStalkFrame` composes the inverse
ordinary-pullback module quotient comparison, the rank-one stalk frame of the
pulled-back sheaf, and the inverse quotient algebra equivalence of the
thickening's local ring. All maps are linear over the original ambient stalk.
It therefore supplies frames for all powers of the same proper extended ideal
at every closed-fibre point. The previously constructed
`lineBundleOfClosedFibreAdicStalkQuotients` applies finite local rank-one
reflection and spreads stalk frames. Universal closedness over the local base
then implies that the rank-one locus is the whole source.

This is internal derived infrastructure for proper formal line-bundle
effectivity. It needs neither completeness of `R` nor flatness of `M` or the
structure morphism, and imposes no projectivity hypothesis. It does not
construct a coherent algebraization of a formal system or a compatible
whole-system comparison.
