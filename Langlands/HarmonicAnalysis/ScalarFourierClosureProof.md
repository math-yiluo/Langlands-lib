# Scalar Fourier closure and sigma-finiteness: proof

`Langlands.HarmonicAnalysis.scalarFourierClosure.{u}` proves the closed
proposition
[`ScalarFourierClosureStatement.{u}`](ScalarFourierClosureStatement.md).
For every field `F : Type u` with the statement's topological and measurable
structures, every `ψ : UnitaryAdditiveCharacter F`, and every
`μ : AdditiveHaarMeasure F`, the hypothesis `IsSelfDual ψ μ` yields both
`MeasureTheory.SigmaFinite μ.measure` and preservation of the actual
Schwartz–Bruhat test space by `fourierIntegral ψ μ`.

The field carries `IsTopologicalRing F`, a Borel measurable structure, local
compactness, the Hausdorff property and total disconnectedness. These are
exactly the hypotheses of the statement. The conclusion includes discrete
fields and requires no extra instance of sigma-finiteness.

## Published prerequisites

[`selfDualSigmaFinite`](SelfDualSigmaFiniteProof.md) proves the first
conjunct directly from self-duality. Its discrete case uses integrability
of the nonzero constant transform of the point indicator to obtain finite
total measure. Its nondiscrete case constructs a countable compact cover
using Haar scaling and continuity of multiplication, then obtains
sigma-finiteness from finiteness of Haar measure on compact sets.

[`compactOpenAnnihilator`](CompactOpenAnnihilatorProof.md) proves that
the set
`{y : F | ∀ x ∈ H, ψ.complex (x * y) = 1}` is compact for each compact open
additive subgroup `H`. It derives finite measure from the integrability
clause of self-duality applied to the indicator of `H`, proves openness
using compactness and the circle half-arc lemma, and applies regularity to
show that a finite-measure open subgroup is compact.

Both prerequisites have the same generic field telescope as the target.
The present module imports their proofs and the target pair unchanged.

## Compact open translation invariance

The private lemma `exists_compactOpenAdd_invariant` gives a compact open
additive subgroup `H` with `f (h + x) = f x` for every `h ∈ H` and every `x`,
for any `f : SchwartzBruhat F`. It applies the published
[`Hecke.TestFunction.commonCompactOpenBiInvariance`](../Representation/Hecke/CommonInvarianceProof.md)
to the singleton containing `f`, viewed on the multiplicative type tag of
the additive group of `F`. The resulting compact open subgroup is converted
explicitly to an `OpenAddSubgroup F`; the left-invariance conclusion gives
the required equation.

## Local constancy

The private lemma `character_locallyConstant` proves that `ψ.complex` is
locally constant. Choose a compact clopen neighborhood `V` of zero inside
the preimage under `ψ` of `Circle.centeredArc (π / 2)`. Such a neighborhood
comes from local compactness, the Hausdorff property and total
disconnectedness. Apply compact open translation invariance to the
published characteristic function of `V`. If `H` fixes that function,
evaluation at zero shows that `H ⊆ V`.

For `x ∈ H`, every natural multiple `n • x` lies in `H`, so every positive
power of `ψ x` lies in the half arc. Mathlib's
`Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two` forces `ψ x = 1`.
The character law then shows that `ψ.complex` is constant on every coset
of the open subgroup `H`.

The private lemma `fourierIntegral_locallyConstant` fixes a Fourier parameter
`y`. Local constancy of the character and joint continuity of
`(z, x) ↦ x * z` imply that near each `(y, x)` the kernel equals its value
at `(y, x)`. Comparing with the kernel at fixed parameter `y` gives local
equality between the two kernels. Compactness of `tsupport f`, through
`IsCompact.eventually_forall_of_forall_eventually`, makes this equality
uniform for every `x` in that support when `z` is sufficiently close to `y`.
Outside `tsupport f`, the function `f` vanishes. Thus the two integrands
agree pointwise everywhere, and integral congruence proves local constancy
of the Fourier integral.

## Compact support

The private lemma `fourierIntegral_eq_zero_of_translation` assumes that
translation by `h` fixes `f`. The additive character law and Haar
translation invariance give

`ψ.complex (h * y) * fourierIntegral ψ μ f y = fourierIntegral ψ μ f y`.

If the character factor is different from one, cancellation implies that
the transform vanishes at `y`. This argument uses the integral identities
directly and adds no sigma-finiteness assumption.

The private lemma `fourierIntegral_hasCompactSupport` chooses a compact
open subgroup `H` fixing `f`. The preceding vanishing result places the
support of the transform inside the annihilator of `H`. Whenever that
annihilator is compact, it is closed because `F` is Hausdorff, so it also
contains the closure of the support. This proves compactness of the
topological support.

## Assembly and provenance

`scalarFourierClosed_of_compactAnnihilator` combines local constancy and
compact support to construct an actual element of `SchwartzBruhat F` whose
underlying function is `fourierIntegral ψ μ f`. Its pointwise equality with
that integral is reflexive, rather than an almost-everywhere identification.
This helper takes compactness of compact-open annihilators as a hypothesis.

The final closed theorem `scalarFourierClosure` introduces exactly the
target's quantified data and self-duality hypothesis. It applies
`selfDualSigmaFinite` to supply the first conjunct and supplies
`compactOpenAnnihilator F ψ μ hself` to the closure helper for the second.
Neither conclusion is added as a premise of the final theorem.

Worker 86 authored this internal derivation from the existing
[`Basic`](Basic.md) interfaces, published Hecke invariance and characteristic
functions, the two published prerequisite proofs, and Mathlib topology and
integration. The inherited Fourier convention is the plus-sign kernel
`ψ.complex (x * y)`, without conjugation. No new literature theorem is
asserted, and the proof does not construct a self-dual measure. It preserves
the statement's universe and adds no continuity of inversion, valuation,
chosen lattice, second countability, nondiscreteness or p-adic assumption.
