# Comparing scheme and sheaf Weil restrictions

Author: Worker 110.

This is derived construction infrastructure for the proof of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Lemma 5.10, printed pp.17–18. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source's proof first represents restriction of an affine scheme by an
affine scheme, and later uses representability of restriction of a
quasi-projective relation scheme. This module identifies the Library's
existing actual representing schemes with its fppf-sheaf restriction
functor. It does not prove the full algebraic-space lemma.

`weilRestrictionPresheafIsoOfEquiv` takes a morphism `g : S' ⟶ S`,
schemes `U` over `S'` and `W` over `S`, and natural equivalences
`Hom(T,W) ≃ Hom(T ×_S S',U)` for every actual scheme `T` over `S`.
It lifts both Hom types by `ULift`, yielding an isomorphism of full
presheaves between `schemeYoneda(W)` and the underlying presheaf of
`weilRestriction(g)(schemeSheaf(U))`. Naturality is the supplied
contravariant naturality law. Its inverse laws are those of the given
equivalences. `weilRestriction_isAlgebraicSpace_of_equiv` transports
the algebraic-space property of a represented scheme along this isomorphism.

`affineWeilRestrictionPresheafIso` applies this construction to the
published `PointTopology.affineWeilRestrictionTestEquiv`. The rings
`R` and `R'` are arbitrary commutative rings, with `R'` a finite
projective `R`-algebra. The input `U` is any actual affine scheme
locally of finite type over `Spec R'`; the test schemes are unrestricted.
No Noetherian, field, finite-free, faithful or finite-presentation
hypothesis is used. Its forward component is exactly the actual
base-change map followed by the universal counit, as recorded by
`affineWeilRestrictionPresheafIso_hom_app`.

`affineWeilRestriction_isAlgebraicSpace` transports the scheme
algebraic-space property along that full presheaf isomorphism.
`affineWeilRestriction_finiteType` transports the identity atlas
of the existing affine finite-type representing scheme. It applies
to every witness of the restricted sheaf's algebraic-space property.

`affineChartWeilRestrictionPresheafIso` similarly applies the published
glued representing equivalence for a relatively separated scheme
locally of finite type whose every finite set of points has an affine
open neighborhood. `projectiveImmersionWeilRestrictionPresheafIso`
specializes directly to a supplied relative immersion into the actual
projective space `ProjectiveSpace R' n`; the published equivalence
already derives separatedness and the affine-neighborhood property
from that immersion. In both constructions the forward component is
the existing glued counit comparison, proved by reflexivity.

The constructions here supply a missing comparison between two published
implementations; they are not additional representability assumptions
and do not alter either implementation. Étale or surjective preservation,
representability of restriction of general algebraic spaces, and its
quasi-separatedness, separatedness and finite presentation remain
obligations of Lemma 5.10.
