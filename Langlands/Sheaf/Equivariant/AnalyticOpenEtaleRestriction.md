# Ordinary restriction of actual analytic étale sheaves

This internal prerequisite constructs the ordinary-topology restriction of
sheaves on the existing actual analytic étale site. It uses the published
étaleness and universal property of canonical open analytic domains. The field
and analytic-space universes remain independent, and the coefficient category
has independent object and morphism universes.

`openEtaleObject` realizes an open subset of the actual underlying analytic
space by its saturated analytic-domain presentation and canonical inclusion.
`openEtaleLift` factors an étale object through an open containing its actual
image. Monicity of the domain inclusion makes such arrows unique. In particular,
`openEtaleMap` realizes inclusions of ordinary opens, and uniqueness proves the
functor laws of `openEtaleFunctor`. Its underlying point map preserves the
ambient point.

For any étale object, the category of arrows from that object into these open
domains is cofiltered. The full open set gives an object. Two factorizations
have a common refinement through the intersection of their opens, since the
image lies in both. Parallel arrows agree because their ordinary-open
inclusions agree. Thus the functor is representably flat.

An ordinary covering sieve covers every underlying point of its open domain.
The realized domain inclusions retain those points, so their images are jointly
surjective in the actual étale site and generate an étale covering sieve. This
proves cover preservation. Together with representable flatness it gives site
continuity.

`etaleUnderlyingSheaf` is the resulting existing categorical sheaf direct image:
its value on an ordinary open is exactly the original sheaf's sections on that
open analytic domain, and restrictions are the original domain-factorization
maps. This unit supplies no comparison of stalks, supports or right-derived
compact sections, and no acyclicity assertion. Its provenance is the internal
application of existing Library domain constructions and Mathlib site-continuity
theorems; no additional original-literature claim is used.
