# Canonical induced coordinates on the actual opposite unipotent group

This derived unit restricts the entire canonical negative-rho induced coordinate
space to the existing opposite dynamic unipotent group and transfers its
negative simple-root degree bound. It combines `CanonicalRhoRootDegree`,
`FrobeniusRootCurveCutoff`, `AffineCoordinateTranslation`, and proved dynamic
representability and smoothness. It uses no external existence or dimension
assertion.

Let `k : Type u` be a field, `G` an affine actual group scheme, and `p` a supplied
split pinning with finite root index and full integral coroot span. Put
`nu = p.rootDatum.Polarization (IntegralWeylVector.rho ...)`. The group `U` is
literally `Dynamic.Affine.unipotentScheme` for
`CommGroupScheme.groupHom (-nu) ≫ p.inclusion`, with its existing actual
inclusion `iU` into `G`.

`canonicalRhoUnipotentRestriction` is the actual coordinate-algebra pullback
along this inclusion. Its evaluation at any `U` point over any relative test
scheme is the original ambient coordinate evaluated after inclusion.

For every simple-root index, the fixed linked negative map represents the
entire intrinsic negative root subgroup. Its pairing with `-nu` is positive
because the corresponding positive simple root pairs positively with `nu`.
Thus its full functor image lies in the actual dynamic unipotent subgroup.
`linkedNegativeSimpleUnipotentMap` lifts this original map through the
representing inclusion. Its composite with `iU` is equal to the original map
as a group-scheme morphism.

Pullback along each translated lifted root curve commutes exactly with
restriction. The resulting polynomial is therefore the original
`linkedNegativeSimpleCurvePolynomial` at the included rational translate.
For an infinite field, every coordinate in the full
`canonicalRhoCovariantSubspace hspan m` consequently has degree at most `m`
on each such curve in `U`. Membership in the full induced space supplies the
bound; no separate polynomial or degree hypothesis is imposed.

Now assume that `k` is algebraically closed, has exponential characteristic
`q`, and `m < q^r`. Suppose the restricted coordinate is right invariant under
every Frobenius-origin point of `U` on every relative test scheme. The ambient
group is smooth by the supplied pinning, and dynamic smoothness makes `U`
smooth. The transferred degree bound therefore meets the hypotheses of
`AffineCoordinateTranslation.leftInvariant_of_originInvariant_natDegree_lt`.
It follows that the restricted coordinate is left invariant under each lifted
original negative simple-root map at every `U` point over every relative test
scheme, including nonreduced tests. This applies in particular to
`m = q^r - 1`, because exponential characteristic is positive.

The split pinning and full integral coroot span remain inputs. Frobenius-origin
invariance remains an explicit premise. This unit does not prove constancy
under the whole group `U`, restriction injectivity, an induced-space dimension
bound, highest-weight existence, or `SteinbergBigCellStatement`. Its purpose is
to supply the actual-object degree and root-invariance inputs to the separate
whole-space argument.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
