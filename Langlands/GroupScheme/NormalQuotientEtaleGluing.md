# Étale descent of affine normal quotients

This internal derived unit proves
`Langlands.GroupScheme.AffineNormalQuotientEtaleGluingStatement` in every
universe. Let `G` be an affine group scheme locally of finite type over any
scheme `S`, and let `i : N → G` be monomorphic on the underlying schemes over
`S`. Suppose `N` is smooth over `S` and the all-test subgroup functor
`SubgroupFunctor.range i` is normal. If affine fppf group quotients by the
pullbacks of this subgroup are supplied on an étale cover of `S`, then there
is an affine group scheme `M` over `S` and an actual homomorphism `G → M`
which is an fppf quotient by precisely `SubgroupFunctor.range i`.

Here affine means affine over the base, and the quotient predicate retains
flatness, scheme-surjectivity, local finite presentation and equality of the
full scheme-kernel range on every test scheme. Neither quotient representability
nor kernel equality is replaced by a statement only about field-valued points.
The étale cover is indexed in the universe of `S`; the theorem holds for every
such universe. No affine or quasi-compact hypothesis is imposed on `S`.

## Implemented proof

`RelativeRoot.IsFppfQuotient.of_iso_square` transports a quotient along
compatible isomorphisms of its source and represented kernel. The three
geometric properties are stable under composition with an isomorphism.
Testing the full kernel on each scheme, the compatible square carries lifts
through one subgroup inclusion to lifts through the other. The lemmas
`baseChange_comp` and `comp_baseChange` apply this to the two directions of
the standard pullback-composition isomorphism. The former also pulls back the
supplied quotient along a further morphism.

`NormalQuotient.exists_affine_fppfQuotient_of_finiteAffineEtaleCover` first
handles a finite affine étale cover of an affine base. Its finite coproduct
is affine and its map to the base is étale, surjective and quasi-compact.
Pullback-composition coherence transports each supplied quotient to the
corresponding open component of that coproduct. The open-cover gluing theorem
then produces an affine quotient over the coproduct. The published
`Descent.exists_affine_fppfQuotient` descends it through the affine fpqc map,
retaining the original subgroup inclusion and its full kernel equality.

`exists_affine_fppfQuotient_of_etaleCover_affineBase` reduces an arbitrary
étale cover of an affine base to this case. Étale maps are open, so the cover
is quasi-compact in Mathlib's cover sense. Mathlib's
`QuasiCompactCover.exists_hom` provides a finite affine refinement. Pullback of
the supplied quotient maps, followed by the composition isomorphism and the
refinement's commuting equations, gives the quotients on this refinement.
Affineness survives these base changes.

`exists_affine_fppfQuotient_of_etaleCover` treats an arbitrary base by its
affine open cover. Pulling the étale cover back to each affine chart and
using the actual pullback square transports the local quotients to that
chart's base-changed group. The affine-base case gives a quotient over each
chart, and open-cover gluing gives the global quotient. Monicity, smoothness,
normality, affineness and local finite type used at these steps are preserved
by base change.

`exists_affine_fppfQuotient_of_pointwise_etale` packages the same conclusion
when, for every point of `S`, one supplies an étale neighbourhood containing
that point in its image and an affine quotient on that neighbourhood. Choosing
these neighbourhoods forms a cover indexed by the points of `S`, to which the
preceding theorem applies. Thus a single affine fpqc cover need not be supplied
as additional input.

## Provenance and scope

This is an internal consequence of the open-cover affine normal quotient
gluing theorem, the published affine fppf quotient descent theorem, standard
pullback coherence, and Mathlib's finite affine cover refinement and finite
coproduct constructions. It introduces no external-source assertion.

The local quotient schemes remain supplied data. This unit neither constructs
them for arbitrary relative parabolics nor proves reductivity or the universal
property of the global quotient. Those remain separate obligations of the
relative parabolic reductive quotient proof.
