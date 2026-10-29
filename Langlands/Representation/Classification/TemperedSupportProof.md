# Discrete-series opposite support of irreducible tempered representations

Author: Worker 387.

`Langlands.glTemperedDiscreteSeriesSupport` proves exactly the closed
proposition
[`Langlands.GLTemperedDiscreteSeriesSupportStatement`](TemperedSupportStatement.md).
It applies to every prime, supplied p-adic field and topological realization,
positive rank, and irreducible analytically tempered complex representation.
The field universe `uF` and original carrier universe `uV` are independent.

The conclusion supplies an ordered block shape `B` and an actual irreducible
representation of its product Levi on a carrier in `Type uV`. This
representation is square-integrable modulo its full center for every Borel
Haar realization, and the original representation has an actual injective
intertwiner into its normalized opposite parabolic induction.

## Implemented proof

The proof bundles the input action as `A := Rep.of π` in the original carrier
universe. The published theorem
[`glWeaklyMinimalStandardPairExistence`](../Exponents/WeakMinimalExistenceProof.md)
supplies a standard block pair with nonempty unitary dual-Jacquet spectrum
and no unitary exponent at any strictly finer concrete conjugate pair.

The intrinsic theorem
`PadicField.TopologicalData.IsWeaklyMinimalDualJacquetPair.isWeaklyCriticalPair`
from [WeakCritical](../Exponents/WeakCritical.md) chooses an occurring unitary
exponent `χ` and proves its weak criticality: each proposed unitary exponent
at a strictly finer pair contradicts minimality. This uses only the
minimal-to-critical implication.

The published closed theorem
[`glWeaklyCriticalDiscreteSeriesSupport`](../Exponents/WeakCriticalSupportProof.md)
then supplies `S : Rep.{uV} ℂ (B.Levi F.Carrier)`, its opposite Jacquet
class-exponent property, prescribed scalar character, full-center all-Haar
square-integrability, and an injective intertwiner into
`T.normalizedOppositeParabolicInduced B S.ρ`. The first component of the
class-exponent property is the required irreducibility of `S.ρ`. Unpacking
the bundled carrier and its existing additive and complex-module instances
gives precisely the target witnesses. The target forgets the additional
class-occurrence and prescribed-character conclusions.

The input analytic predicate, the product-Levi action, the entire all-Haar
square-integrability clause, and the actual embedding pass through unchanged.
The opposite induction retains inverse upper half-modulus covariance; its
Jacquet input is the actual opposite quotient with positive upper
half-modulus action. No tensor decomposition or change of Haar measure enters
this assembly. Both imported support prerequisites are actual closed
theorems, so no theorem-valued premise remains.

## Provenance and scope

The motivating original is A. J. Silberger, *Introduction to harmonic
analysis on reductive p-adic groups* (1979), registered as
`silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Corollary 4.5.11, printed pp.189–190 (one-based PDF pp.195–196), gives
discrete-series opposite support and its prescribed weakly critical-exponent
refinement. The paragraph immediately before the corollary gives weak
minimality and its implication to criticality; the proof begins by choosing
a weakly critical pair, for example a weakly minimal one. Those original
pages were read and their formulas checked in page images. No source-specific
errata file was present in the project or current Library notes at the final
assembly check.

This module is an internal logical assembly of the two published proofs and
the intrinsic implication. Their paired explanations describe the bounded
minimal-pair selection and the maximal-layer quotient and analytic L² proof.
The present proof neither reasserts those analytic results as assumptions nor
uses the critical-to-minimal converse, the aggregate weak-critical refinement,
tempered-block exhaustion, tempered unitarity or genericity, regular
Langlands exhaustion, or equal-exponent grouping. It proves the support
clause only; uniqueness and summand equivalences are separate statements.
