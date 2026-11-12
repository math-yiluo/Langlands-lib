# Convolution of compactly supported distributions

This definition unit implements the constructions of Renard II.3.10,
printed pp.50–51 / PDF pp.56–57. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
All declarations are in `Langlands.HarmonicAnalysis.Distribution`.

`dirac x` is actual evaluation at `x` in the existing full algebraic dual.
`compactDirac x` is the same distribution in the published
`compactlySupported` submodule: a test vanishing at `x` is annihilated,
so the topological support is contained in the compact singleton `{x}`.
The construction requires the same Hausdorff, locally compact and totally
disconnected hypotheses as that compact-support submodule.

`onSupport T` descends a compactly supported distribution to its own actual
closed support with the published `closedPushforwardSupportedEquiv`.
`multiplicationPullback T S` pulls a test `f` back to
`(x, y) ↦ f(xy)` on `support T × support S`. This product is compact, so
the pullback is a genuine test even though multiplication on the whole
group need not be proper. `convolutionDistribution T S` evaluates the
already published tensor product `tensor (onSupport T) (onSupport S)` on
that pullback.

This is a support-restricted implementation of the source's formula
`⟨T * S, f⟩ = ⟨T ⊗ S, (x,y) ↦ f(xy)⟩`. To make the latter pairing meaningful,
the source uses compactness of `T ⊗ S` and extends its evaluation from tests
to locally constant functions. Here the distribution is first descended
to the product of the two compact supports, where the pullback is itself a
test. No tensor-support theorem is assumed and no ambient cutoff is chosen.
The identity with the source formula using the existing ambient tensor and
compact-support pairing is a separate correspondence statement obligation.

The theorem `support_convolutionDistribution_subset` proves the bound
`support (T * S) ⊆ support T * support S`: if a test vanishes on the product,
its multiplication pullback is the zero test, so its convolution evaluation
vanishes. The published annihilator-to-support implication gives the bound.
The product of the compact supports is compact and the convolution support
is closed, giving the compactness needed by `convolution`, an operation on
the original `compactlySupported` carrier. This well-definedness proof
establishes II.3.10 Proposition (i) for the constructed operation. No
associativity or algebra instance is assumed or supplied.

For any full distribution and any test, `leftConvolveTest T f` and
`rightConvolveTest f T` are the scalar functions given by evaluating the
published translated inverted tests:

- `leftConvolveTest T f x = T (g ↦ f(g⁻¹x))`;
- `rightConvolveTest f T x = T (g ↦ f(xg⁻¹))`.

The expressions in parentheses are genuine tests, implemented by the
existing translations and inversion; no Haar factor is inserted. Their
local constancy as functions of `x` remains a statement obligation.

`leftConvolveSmooth T f` and `rightConvolveSmooth f T` use the same kernels
for a compactly supported distribution and an arbitrary locally constant
function. They use the existing `compactSupportPairing`, so they are
defined without requiring the kernel to have compact support. These maps
currently return scalar functions. Their local constancy, agreement with
the test formulas and compact support when `f` is a test are separate
statements. The remaining Proposition clauses, the unit and Dirac
identities, and the II.3.10 Lemma likewise remain to be stated and proved.
