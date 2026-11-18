# Conditional étale gluing of analytic morphisms

Author: Worker 790.

This module proves categorical consequences of explicitly supplied sheaf
properties for the presheaves of full analytic morphisms on the published
small étale sites. It does not prove the sheaf properties themselves.
It assumes no categorical pullback existence and imports only published
`EtaleSite`.

`hom_ext_of_etale_local_eq` forms the sieve of arrows on which two analytic
morphisms agree, over the identity object of the source's small étale site.
The existence of an étale lift through every source point on which they
agree makes this sieve covering. Separatedness of the given Hom sheaf
then gives equality globally.

`exists_hom_of_etale_local_lifts` glues local lifts of a pair of morphisms
through a pair of jointly monic projections. Its hypotheses require that
at every source point there is an étale source lift through that point
carrying a morphism satisfying both projection equations. The proof forms
the sieve of étale objects carrying such lifts. It is downward closed by
precomposition and covering by the pointwise local-lifting hypothesis.
Choose a lift on each arrow. Joint monicity makes these choices compatible.
The supplied Hom sheaf to the proposed apex amalgamates them; separatedness
of the two Hom sheaves to the projection targets proves both equations
for the amalgamation. Joint monicity and local lift existence are explicit
hypotheses, not conclusions about the analytic category.

`isPullback_of_etale_local_lifts` applies this gluing construction to every
compatible cone over a commuting square. The glued morphisms supply the
lifts in `PullbackCone.IsLimit.mk`; joint monicity proves their uniqueness.
Thus the square is a categorical pullback. This criterion keeps the
geometric local-lifting and uniqueness obligations visible and does not
use a global pullback object or a base-change theorem.

## Provenance: internal

These are direct categorical deductions from the definitions of sheaf,
small étale site and joint monicity. They are proof reductions for the
algebraic-space analytification fibre-product problem, rather than new
literature assertions. The literature supporting the separate sheaf
hypothesis is described in `EtaleHomSheafStatement.md`; it is not used
as an unproved theorem here.
