# Preservation of open immersions from analytic Hom descent

For a complete ultrametric nontrivially normed field `K : Type u`, the
module gives the open-immersion preservation implication for a
compatible map `F : Y' ⟶ Y` of analytifications of algebraic spaces
`X'` and `X` over `Spec K`, assuming `X'` is separated. The theorem
`openImmersion_of_isOpenImmersion_of_etaleHomSheaf` uses the sheaf
property of analytic Hom presheaves on the small étale site as its
analytic premise. The analytic spaces are in universes `u, u, u`.

## Implemented proof

The construction `openImageIsoOfEtaleSourceCoverOfHomSheaf` starts with
an étale source cover of a map `f` whose composites are étale. The
range of `f` is the union of the open ranges of the composites, so it
has an open analytic domain. The map `f` and the composites lift to
that domain. Each lifted cover map is étale by cancellation along the
domain inclusion, since its composite with the inclusion is one of the
given étale maps. Their point maps are jointly surjective onto the domain.

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

The original entry points `openImageIsoOfEtaleSourceCover` and
`openImmersion_of_isOpenImmersion_of_homSheaf` still accept
`LocalizedEtalePullbackStatement` and delegate to the strengthened results.

## Provenance

This is a deduction from the published affine-test definition of
analytification, étale domain cancellation and analytic Hom descent. Its use of
étale descent of morphisms for gluing analytic quotients follows the
mechanism in Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces*, §4.1, printed pp. 18–19. The algebraic closed affine
overlap is supplied by `hasClosedAffinePointPullbacks_of_isSeparated`.
