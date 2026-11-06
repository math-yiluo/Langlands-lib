# Unitarity adapters for actual rational parabolics

Author: Worker 346. This is internal supporting work for Renard VII.2.6.
It does not prove the unconditional corollary.

`rationalSquareIntegrableUnimodularForm` constructs a positive invariant form
on an irreducible smooth representation of the actual connected reductive
rational-point group. It assumes the ambient modular character is trivial
and square-integrability modulo the full center for every Haar measure.
Hausdorffness comes from the point topology; second countability comes from
the published finite-type rational-point theorem. The proof chooses the
canonical quotient Haar measure, derives its right invariance from ambient
unimodularity, and applies the published square-integrable unitarity proof
with compact-open cofinality from local compactness and the nonarchimedean
group condition. No carrier topology or completion is introduced.

`leviInductionUnimodularForm` transports a form along the inverse of the
actual Levi-point equivalence and applies the published general normalized
induction integral form. Its hypotheses are compactness of the actual
parabolic quotient, triviality of the ambient modular character, and the
full parabolic modular-character identity for the given radical. Closedness,
local compactness and Hausdorffness of the actual subgroups come from the
represented closed immersions and the canonical point topology.

Both the field universe and representation-carrier universe remain arbitrary.
The induced carrier has universe `max u v`, as in `leviInductionFunctor`.
These are derived adapters of Library constructions, following the form
restriction route described in the VII.2.6 corollary. They retain geometric
premises explicitly; no unconditional reductive unimodularity, quotient
compactness or parabolic modulus theorem is supplied here.
