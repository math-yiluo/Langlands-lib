# Natural projectors and actual subquotients

Author: Worker 173. This is an internal algebraic construction for the eventual proof of
`LeviQuasicuspidalDecompositionTheorem`. It is not a proof of that published target,
and it makes no assertion that a quasicuspidal natural projector exists.

The generic lemma works over any commutative coefficient ring, with independent
group and carrier universes. Given a natural idempotent family of actual
intertwiners, it takes the actual invariant range and kernel. Mathlib's
idempotent linear map theorem proves that their underlying submodules are
complementary. Naturality with respect to the kernel inclusion proves that the
projector vanishes on the kernel. Naturality transports this vanishing along an
injective subrepresentation map and a surjective quotient map. The actual
isomorphism in `SmoothRep.IsSubquotient` then transfers it to any represented
subquotient. If the projector is also the identity on that subquotient, its
carrier is subsingleton.

The abstract property P is required on every projector image and must imply
that the projector acts as the identity. These hypotheses are internal assembly
inputs only; the final target must construct and prove the quasicuspidal family
without theorem-valued assumptions. No finite length, admissibility, or closure
of P under subquotients is used in this algebraic step.

This companion module is reviewed with `PointwiseProjectorSum`, whose constructor
and conditional decomposition theorem use this range/kernel argument. It is a
partial algebraic construction unit and does not discharge the main task's
unconditional product-Levi decomposition proposition.
