# Preservation of open immersions from analytic Hom descent

For a complete ultrametric nontrivially normed field `K : Type u`, the
module gives the open-immersion preservation implication for a
compatible map `F : Y' ⟶ Y` of analytifications of algebraic spaces
`X'` and `X` over `Spec K`, assuming `X'` is separated. It uses
`LocalizedEtalePullbackStatement` and the sheaf property of analytic Hom
presheaves on the small étale site as explicit premises. The analytic
spaces are in universes `u, u, u`.

## Implemented proof

The general construction `openImageIsoOfEtaleSourceCover` starts with
an étale source cover of a map `f` whose composites are étale. The
range of `f` is the union of the open ranges of the composites, so it
has an open analytic domain. The map `f` and the composites lift to
that domain. Each lifted cover map is the pullback of its composite
along the open domain inclusion. The étale pullback premise makes
these lifted cover maps étale, and their point maps are jointly
surjective onto the domain.

The hypothesis on common refinements of cover maps ensures the
original maps to the source of `f` agree over the open image domain.
Analytic Hom descent glues them to a map from the domain to the
source. Uniqueness of the respective amalgamations verifies both
inverse identities, using the étale cover of the source and the
étale cover of the domain. The construction returns the isomorphism
with the factorization equality.

For the application to an algebraic open immersion, the source
family consists of all étale affine test points of `X'`. Their
composites with the open immersion are étale over `X`, so
`IsAnalytification.etale_map` gives étaleness of their analytic
composites with `F`. Separatedness of `X'` supplies another affine
test point representing the overlap of any two family members.
An open immersion is monic, so this is also their overlap over
`X`. The pullback axiom for both analytifications gives the same
analytic overlap over `Y'` and `Y`. Thus every pair of lifts equal
over `Y` factors through the overlap and is already equal over
`Y'`. Applying the general construction proves `openImmersion F`.

## Provenance

This is a deduction from the published affine-test definition of
analytification and the two explicit analytic premises. Its use of
étale descent of morphisms for gluing analytic quotients follows the
mechanism in Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces*, §4.1, printed pp. 18–19. The algebraic closed affine
overlap is supplied by `hasClosedAffinePointPullbacks_of_isSeparated`.
