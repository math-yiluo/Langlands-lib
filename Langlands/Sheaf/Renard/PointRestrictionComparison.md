# Actual point restriction and the original stabilizer stalk

Worker 151, Task 5297. Derived comparison for Renard III.3.2, printed p.84 /
PDF p.90, the restriction-functor paragraph and its sentence identifying point
restriction with the original smooth stabilizer representation. Source:
`renard-2026-representations-groupes-reductifs-padiques`, French edition dated
9 July 2026, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This unit completes the implementation comparison between the existing actual
subgroup-space restriction and the existing original-stalk functor.

All names have prefix
`Langlands.Sheaf.Renard.SectionActions.PointRestrictionComparison`.
The group and base have universe zero, and the coefficient field is actual ℂ.
The algebraic point comparison assumes a topology on the group, a jointly
continuous action on the base Y, a subgroup Q, a point y, and an explicit proof
that Q fixes y. The smooth comparison additionally assumes that G is a
topological group and locally profinite, Q is closed, and Y is locally
profinite. These are the hypotheses of the already published smooth
subgroup-space restriction. A singleton in a Hausdorff space is closed, so
the source's locally closed restriction includes this case. Countability at
infinity is not required for point restriction; it is retained separately for
the later transitive-action statement. The singleton action and its
continuity are the original PUnit action and the existing SingletonSheaves
instance.

`singletonNhdsTerminal` observes that the whole open singleton is terminal
also in the opposite category of its point's neighbourhoods: every
neighbourhood is the whole singleton. The original global germ is therefore
an isomorphism by the colimit property, as recorded by `globalGerm_isIso`.
`allSectionsEquiv` forgets only the compact-support subtype of an original
global singleton section; its inverse gives that same section its finite
support proof. `compactGermIso` composes this equivalence with the original
global germ. Thus it is exactly the original compact global germ, without
changing either section or stalk objects.

`compactGermIso_action` uses the published labelled germ formula with the
original inverse-labelled section arrow. It proves that the compact germ
commutes with the original compact-section and stalk actions.
`compactGermIso_naturality` is the original compact-germ naturality for every
sheaf map.

`pointMap` is the literal continuous constant map from PUnit to y.
`pointMap_equivariant` derives its Q-equivariance from the given fixed-point
condition. `pointStalkIso` applies InverseImageStalks.stalkIso to the original
subgroup restriction and this singleton map. Its source is definitionally
the original ambient sheaf's stalk at y; its target is the original stalk of
the actual subgroup-space inverse-image sheaf on PUnit. The action and
naturality laws retain the original subgroup labels and original induced
stalk maps.

`moduleIso` takes compact sections of this actual singleton restriction,
applies its original compact global germ, and then applies pointStalkIso's
inverse. `moduleIso_pointStalkIso` states this exact factorization.
`moduleIso_naturality` follows by cancelling the invertible point-stalk map,
then using the two original germ naturality equations. Similarly, `actionIso`
is an isomorphism between the original compact-section Q-action and the
original fixedStalkAction. Cancelling the same map reduces its commutation
law to compactGermIso_action and pointStalkIso_action. No replacement stalk
action is installed.

`actionsIso` makes this isomorphism natural in the action category.
`algebraicIso` applies the published equivalence between actions and
representations to identify the actual subgroup-space restriction followed
by the existing compact-section functor with fixedStalkFunctor Q y hfix.
`smoothIso` lifts exactly this natural isomorphism through the full smooth
representation category. Its source is the existing
smoothSubgroupSpaceRestriction along pointMap, followed by the existing
Γ_c functor on the singleton; its target is the original
smoothFixedStalkFunctor. This is the source's point-restriction identification
with the original smooth stalk, including original maps.

This comparison does not claim that every singleton action sheaf is recovered
from its compact sections, the general singleton categorical equivalence,
the sheaf/test-module equivalence, the induction/coinvariant sheaves, or the
main III.3 theorem statements. Those constructions and statements remain
separate units.
