# Scalar compact-picture integration for standard GL parabolics

Authors: Worker 166 and Worker 117. Worker 117 specified the standalone scalar
interface in task `1d0b7d25-f62a-449c-9207-b07a3d358d5b`; Worker 166 formalized it
and wrote this explanation.

`Langlands.GLParabolicCompactScalarIntegralStatement` is a closed proposition
definition awaiting proof. It specifies a single compact-picture integration
functional for each actual standard block parabolic, independently of any
inducing representation.

## Exact assertion and conventions

For every prime `p`, every `F : PadicField.{uF} p`, every supplied compatible
realization `T : F.TopologicalData`, every positive rank `n` and every ordered
block shape `B`, set `G = GL_n(F)` and `P = B.parabolic F.Carrier`. The topology
is exactly `T.topology`, with the existing general-linear topology and group
structure. The field universe `uF` is arbitrary. The assertion includes
one-block shapes, whose parabolic is the entire group.

There exist an actual open subgroup `K` of `G` and a measure `mu` on its Borel
measurable space with the following properties:

- The underlying subset of `K` is compact.
- Every `g` in `G` has a factorization `g = q k`, with `q` in `P` and `k` in `K`.
- `mu` is a Haar probability measure on `K`. The `IsHaarMeasure` predicate
  includes positivity on every nonempty open set, so full support is part of
  the assertion.
- For every scalar function `phi : G -> C` that is locally constant and obeys
  `phi(q x) = delta_P(q) phi(x)`, and for every ambient element `g`, the function
  `k |-> phi(k g)` is integrable and
  `integral_K phi(k g) dmu = integral_K phi(k) dmu`.

Here `delta_P(q)` is precisely the existing full positive block modulus
`T.leviModulus B (B.leviProjection F.Carrier q)`, coerced from nonnegative
real units through the nonnegative reals and reals to the complex numbers.
It is not the positive half used in normalized induction and not the inverse
character. The block formula is

`delta_P(m) = product_(i<j) |det m_i|^(size j) / |det m_j|^(size i)`.

The determinant norms are the existing residue-normalized norms, using the
`q^(-valuation)` convention. The action on scalar functions is right
translation `phi(x) |-> phi(x g)`, while covariance is on the left by the
actual upper block parabolic. Two positively half-normalized induced factors,
paired by evaluation against the algebraic smooth dual or by a Hermitian
form, produce this full-modulus covariance.

`K` and `mu` are chosen before `phi` and `g`; the same scalar functional thus
works for all inducing carriers. Local constancy and covariance are the only
conditions on `phi`. No global compact-support condition is added: `P \ G` is
compact in this setting. The conclusion includes all ambient translations,
with no restriction to elements of `K`. The Borel measurable structure is
installed explicitly on `K`, rather than chosen as additional data.

## Original source and derived formulation

The registered original is Bill Casselman, *Introduction to the theory of
admissible representations of p-adic reductive groups*, draft May 1, 1995,
source `casselman-1995-admissible-representations`, SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The retained file is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
Sections 2.4 and 3.1, printed/PDF pages 26–27 and 32–33, were read directly;
the formulas on pages 32–33 were also checked in the page images.

Theorem 2.4.2, page 27, constructs a right-translation-invariant scalar
functional `I_delta` on compact induction of the subgroup modulus when the
ambient group is unimodular. Section 3.1, page 32, fixes the positive
half-modulus convention for normalized parabolic induction.
Proposition 3.1.1 uses a good compact subgroup with `G = P K`.
Proposition 3.1.3, pages 32–33, identifies the pairing functional with integration
over that compact subgroup. Its proof identifies `I_delta` with the compact
average on scalar functions transforming by the full modulus: the displayed
normalized induction of `delta_P^(1/2)` has total covariance `delta_P`.
Proposition 3.1.4 then uses positivity to obtain the induced Hermitian form.

This declaration is a derived standalone scalar interface for that argument,
specialized to actual standard general linear parabolics. It is not a separate
verbatim theorem in the source. Compactness permits probability normalization
of Haar measure; multiplying a translation-invariant functional by this fixed
normalizing scalar preserves its invariance. Local constancy gives continuity
and integrability of each translated scalar function on compact `K`.
This formulation separates the scalar existence and invariance assertion from
any assertion about an induced representation or its smooth dual.

## Existing inputs and remaining proof obligations

The Library already supplies the following reusable constructions and proofs:

- `Langlands.Parabolic.isCompact_integralRange` and
  `quotientMap_image_integralRange` in
  `Langlands.Representation.Parabolic.QuotientCompactProof` give compactness of
  the integral subgroup and its surjection onto `P \ G`.
  `GeneralLinear.Iwasawa.exists_mul_upperTriangular` and
  `BlockShape.mem_parabolic_of_isUpperTriangular` give the actual factorization.
  `Iwasawa.integralRange_succ` and `Conductor.levelSubgroup_zero` identify the
  positive-rank integral subgroup with the existing compact open level subgroup.
- `Langlands.RankinSelberg.generalLinearHaarRightInvariant` in
  `Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity` gives
  right invariance of actual GL Haar measure in positive rank.
- `Langlands.glBlockModulusHaar` in
  `Langlands.Group.GL.BlockModulusHaarProof` identifies the radical Haar scaling:
  pushforward by Levi conjugation multiplies the measure by the inverse of
  `T.leviModulus B m`. That inverse is compatible with the forward-pushforward
  convention and does not reverse the covariance in this statement.

These results do not by themselves establish this new proposition. A proof
must still construct the parabolic Haar disintegration or another valid
scalar integration argument and identify the compact average with the
right-invariant functional. It must establish the probability Haar choice,
integrability, and every ambient translation identity, with the stated
normalizations. `QuotientIwasawaIntegrationStatement` concerns the unipotent
quotient and is a different target.

This pair supplies no proof of scalar integral existence, normalized-induction
unitarity, natural induction duality, refined product-Levi integration,
second adjointness, Jacquet multiplicity comparison, or the irreducible-head
consequence. In particular, the natural induction-duality target also needs
rank zero, arbitrary refined Levi groups, actual perfect pairings, and
naturality on intertwiners; those are separate obligations.
