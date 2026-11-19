# Domain factorizations in localized pullbacks

`LocalizedEtaleBaseChangeStatement K` expresses the base-change clause
for étale morphisms in Corollary 3.3.8 of Berkovich's *Étale cohomology
for non-Archimedean analytic spaces* (1993, printed p. 63). In any supplied
full pullback square in `LocalizedCategory.{u,v,v}`, if the first leg of
the cospan is étale then the projection to the other factor is étale.
The field universe and the common space and atlas-index universe are
independent. The statement uses the existing localized `etale`
predicate and the standard morphism-property class for base change.

The intersection of the inverse images of two analytic domains in an
actual localized pullback is the full pullback of the restricted legs.
The proof pastes the analytic-domain intersection square and the
domain-preimage squares.

Under the base-change hypothesis, a domain in an étale envelope pulls
back to an actual inverse-image domain in the pulled-back envelope.
For two factors given by domains of étale envelopes over the same base,
their pullback is the intersection of the two inverse-image domains in
the pullback of the envelopes, which is étale over the base. Uniqueness
of full pullbacks identifies the factorizations for any supplied cone.

For the local versions, finite neighbourhood families are pulled back
along the projections. The inverse-image domains through a point, or
the pairwise intersections of such domains, again have neighbourhood
union by continuity of the projections.
