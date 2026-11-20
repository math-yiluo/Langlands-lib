# Ordinary restriction given étaleness of open domains

Let `X` be a localized analytic space over a complete ultrametric normed field.
The constructions in `OpenEtaleRestriction` take explicit
`hOpen : EtaleOpenDomainStatement X`, which asserts that every canonical open
analytic domain inclusion is étale.

`openEtaleObject` pairs each canonical inclusion `domainι` with its étaleness
witness from `hOpen`. `openEtaleMap` uses `domainLift` to factor this inclusion
through a larger open. A morphism to an open-domain object is determined by its
composite with the monomorphism to `X`. This proves the identity and composition
laws of `openEtaleFunctor`. On points `openEtaleMap_apply` gives the ordinary
subtype inclusion.

For each étale object, the category of its maps into the open-domain objects
is cofiltered. The full open gives an object, two maps factor through the
intersection of their opens, and parallel maps of ordinary opens agree. This
gives representable flatness. Given an ordinary covering sieve and a point of
the target domain, a covering open containing the point supplies a preimage
under its realized inclusion. The jointly surjective criterion for
`etaleTopology X` then gives cover preservation. Mathlib combines
representable flatness and cover preservation to give site continuity.

`etaleUnderlyingSheaf` is the continuous sheaf pushforward. Its underlying
presheaf is exactly precomposition with `openEtaleFunctor.op`, so its sections
and restrictions are those of the original sheaf evaluated on the canonical
open domains and their lifts. Continuity gives the sheaf condition on the
ordinary topology. The coefficient category has independent object and
morphism universes.

This is the full-space case of the functor from open subsets to the étale site
in Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
§4.2, paragraph before Proposition 4.2.4, printed p. 87, with the covering
criterion from §4.1, printed p. 82. The Lean construction generalizes the
Library's ordinary restriction by abstracting its open-domain étaleness proof
and retaining its domain lifts and Mathlib site argument.
