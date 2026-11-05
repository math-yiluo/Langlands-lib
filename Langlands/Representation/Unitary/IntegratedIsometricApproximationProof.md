# Proof of strong approximation for actual integrated isometric actions

Worker 116 authored the exact theorem
`Langlands.Analysis.integratedIsometricApproximation :
IntegratedIsometricApproximationStatement`. Worker 1678 adopts the complete
proof from Worker 116's shared parent draft 27 for this dedicated proof
task, with the published target and imported construction unchanged.
Worker 116 remains an actual coauthor.

Fix a vector x and a positive real number ε. Continuity of its orbit
at the group identity, together with the homomorphism's identity law,
gives the neighborhood

U = {g : ‖π(g)x − x‖ < ε/2}.

The support hypothesis puts the support of f_n inside U for every
sufficiently large n. The proof works at each such index.

`integral_smul_const`, `integral_complex_ofReal`, and the scalar
normalization show that the integral of (f_n(g):ℂ) • x is x.
The weighted orbit is integrable by the imported constructor's
`isometricActionIntegrand_integrable`; the weighted constant is
integrable by `Integrable.smul_const`. Thus `integral_sub` legitimately
expresses T_n x − x as the Bochner integral of
(f_n(g):ℂ) • (π(g)x − x). This subtraction uses actual integrable
functions rather than relying on a totalized undefined integral.

If f_n(g) is zero, the error integrand is zero. Otherwise g belongs to U.
Nonnegativity of f_n(g), `norm_smul`, and `Complex.norm_real` then give
the pointwise bound by f_n(g)ε/2. The scalar bound is integrable because
f_n is integrable. `norm_integral_le_of_norm_le` and normalization bound
the error norm by ε/2, which is strictly less than ε. The metric
characterization of filter convergence finishes the proof. Group and
vector-space universes remain independent.

This implements the elementary Bochner estimate described in the paired
statement. Its original motivation is Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), Definition 3.4.1 and Corollary
3.4.2, printed p.86, one-based PDF p.102, and the Dirac-sequence
discussion in section 9.3, printed p.246, one-based PDF p.258.
The registered source is `getz-hahn-2024-automorphic-representations`,
SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete October 2026 author errata is registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
Those original passages and the complete errata were read directly
during preparation of the statement; that edition contains no correction
to these passages.

As the statement explains, the internal complete normed-space argument
uses Bochner integration with explicit AE strong orbit measurability
and scalar integrability, whereas the source uses a Pettis construction
with continuous compactly supported weights and right Haar measure.
No translation identity occurs in the implemented estimate, so arbitrary
measures and the exact orbit hypotheses suffice. The proof does not
construct the weights, prove a Pettis comparison, self-adjointness or
compactness, supply an automorphic Hilbert realization, or establish a
spectral decomposition.
