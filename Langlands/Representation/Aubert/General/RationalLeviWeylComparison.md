# Standard Levi Weyl images on actual rational points

This derived consumer construction compares the two existing standard Levi
Weyl constructions through the representative-preserving ambient equivalence
in `RationalWeylComparisonTarget`. Both exact ambient comparisons remain
explicit hypotheses: scheme normalizer points must equal the normalizer of the
literal torus point image, and scheme centralizer points must equal its full
point centralizer. This module does not prove either universal comparison.

All declarations are in
`Langlands.Aubert.General.RationalPointFamily`. The base is any field `k`,
`T` is a commutative group scheme over `Spec k`, `G` is a group scheme with
affine structure morphism, and `i : T.toGrp ⟶ G` is the actual torus map.
The cocharacter `ν` defines the published simple relative roots, and an index
`I` is a finite subset of their actual membership subtype. No finite instance
on the whole simple-root subtype is required or manufactured.

`pointStandardWeyl i ν I` is the range of the published injective map
`Group.RelativeWeyl.inclusion` from
`LeviWeyl i ν I = WeylIn (torusPoints i) (levi i ν I)` into `Weyl i`.
Its membership lemma says precisely that a class has a normalizer
representative whose ambient rational point lies in the exact published
standard Levi at `rootSet i ν I`. The numerator is the intersection of
the point-image normalizer with that Levi; the denominator is the full
point centralizer restricted to the numerator.
`pointCentralizer_le_levi` proves, under the centralizer comparison, that
this entire centralizer is contained in the standard Levi. It transports
the existing unconditional scheme-centralizer containment.

`weylEquiv_map_schemeStandardWeyl` proves that the image of
`schemeStandardWeyl i ν I` under the ambient `weylEquiv` is exactly
`pointStandardWeyl i ν I`. In each direction the proof uses the same
ambient rational point as normalizer representative and the same Levi
membership proof. `standardWeylImageEquiv` is the resulting equivalence
between the two image subgroups; its application formula is recorded.

`leviWeylEquiv` then identifies the actual Levi quotient with the
scheme-standard Weyl subgroup. It composes the equivalence onto the range
of the injective actual inclusion with the inverse of
`standardWeylImageEquiv`. The proved `weylEquiv_leviWeylEquiv` makes the
square with the two ambient inclusions commute, and `leviWeylEquiv_mk`
records preservation of each normalizer representative. Thus these are
compatible actual quotient maps, with no arbitrary labeling of Weyl elements.

No maximal-split, reductivity, local-field or positivity hypothesis is
needed for these conditional algebraic constructions beyond the displayed
ambient comparisons. They give no Coxeter system, reflection or root-sign
realization, standard/dynamic equality, general finiteness, endpoint identity,
or representation-theoretic assertion. In particular, equality of the
empty standard Levi with the centralizer remains a separate structural
target; it is not inferred from containment.

The source motivation is Renard, *Représentations des groupes réductifs
p-adiques*, version of 9 July 2026, V.4.1 and V.4.3.1, printed pp.118–119
/ PDF pp.124–125. These passages use the full-centralizer relative Weyl
quotient and the standard Levi Weyl inclusion. The comparison between the
published scheme-point image and the actual subgroup quotient is an internal
derived implementation result, rather than a separately numbered assertion
of Renard. The Lean proof uses quotient induction, the exact membership
descriptions, the representative formula for `weylEquiv`, restriction of
a multiplicative equivalence to a subgroup image, and injectivity of the
existing Levi quotient inclusion.
