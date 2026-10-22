# Real compactly supported averaging on a left quotient

This module constructs averaging on the existing
`Langlands.QuotientIntegration.LeftQuotient H`, with cosets `H g` and its
existing quotient topology. It leaves `QuotientMeasure` unchanged.
The main construction is `quotientAverageRealPositive`, a positive real
linear map from `C_c(G, ℝ)` to `C_c(LeftQuotient H, ℝ)`.
`quotientAverageRealLinear` is its underlying linear map.

The hypotheses for these bundled maps are a locally compact topological
group `G`, a subgroup `H` whose underlying set is closed, a Borel measurable
structure on `H` with its subtype topology, and a right-invariant measure
`μH` finite on compact sets. Thus the requested locally compact Hausdorff
case with a regular right-invariant Haar measure is included. The construction
needs neither nonzero measure nor the remaining Haar or regularity properties;
it also does not need ambient Hausdorffness. Quotient Hausdorffness follows
from `leftQuotient_t2Space H hH` in `QuotientTopology`. No second countability,
sigma compactness, quotient measure, or assumed continuity of averaging
enters any conclusion. No measurable structure on the quotient is needed
for this continuous-function construction.

## Actual integrals and API

`orbitAverageReal H μH f g` is the actual real Bochner integral
`∫ h : H, f (h.val * g) ∂μH`. This definition is available for arbitrary
functions and measures with the needed measurable structure; it does not
assert integrability. Right invariance proves `orbitAverageReal_left_mul`,
and `quotientAverageReal` uses the published `descend` to give a function on
left cosets. `quotientAverageReal_mk` is its exact evaluation formula.

`quotientAverageRealPositive_apply` and `quotientAverageRealLinear_apply`
identify the bundled operators pointwise with this actual average.
`quotientAverageRealLinear_mk` states the exact integral formula at every
representative. Addition and real scalar compatibility are proved as the
linear-map fields, using fiber integrability for addition and the Bochner
scalar identity. Monotonicity is the positive-map field, proved by integral
monotonicity. `quotientAverageReal_nonneg` states pointwise nonnegativity
for arbitrary nonnegative functions; `quotientAverageRealLinear_nonneg`
is its bundled counterpart. Standard positive-linear-map and linear-map
APIs provide the resulting algebraic identities.

`quotientAverage_ofReal` identifies the existing complex `quotientAverage`
of `g ↦ (f g : ℂ)` with the complex embedding of the real average. It uses
Mathlib's `integral_complex_ofReal` and holds for the actual total integrals,
including before integrability is established. `quotientAverageReal_rightTranslate`
proves the right-translation identity directly on representatives by
associativity.

## Implemented analytic proofs

`hasCompactSupport_subgroup_mul_of_hasCompactSupport` applies the closed
embedding `h ↦ h.val * g` to any compactly supported function with a zero-valued
codomain. `integrable_subgroup_mul_of_hasCompactSupport` adds continuity and
a normed additive group codomain to obtain fiber integrability against a
measure finite on compact sets. The codomain has an independent universe;
no completeness, normed scalar module, or countability is required. This
includes complex continuous compactly supported functions used by the
quotient-measure bridge. `hasCompactSupport_subgroup_mul` and
`integrable_subgroup_mul` specialize these facts to bundled real functions.

For `continuous_orbitAverageReal`, fix a representative `g` and a compact
neighborhood `U` of `g`. All potentially nonzero integrands for parameters
in `U` have their subgroup variable in
`K = Subtype.val ⁻¹' (tsupport f * U⁻¹)`.
The closed subgroup embedding makes `K` compact. Joint continuity of
`(p,h) ↦ f(h.val*p)`, together with this common compact support, gives
continuity on `U` by Mathlib's
`continuousOn_integral_of_compact_support`. Since `U` is a neighborhood,
this proves continuity at `g`. This Mathlib theorem uses compact uniformity
and does not require first or second countability of the parameter space.
`continuous_quotientAverageReal` then descends continuity through the quotient
topology.

`support_quotientAverageReal_subset` proves that the nonzero set of the
average lies in the quotient image of `tsupport f`: outside that image every
fiber value vanishes. This result does not require local compactness or
finiteness of the measure on compact sets. The image is compact and is
closed because the closed-subgroup quotient is Hausdorff. Taking closures
therefore proves `hasCompactSupport_quotientAverageReal`, with the same
weaker analytic hypotheses. These facts supply the bundled compact-support
field; no analytic field is supplied as a hypothesis.

## Source and provenance

Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, second edition,
2015, section 2.6, equation (2.47) and its following paragraph, printed page
61 / retained PDF page 74. Registered source
`folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The cited original page was read directly. No erratum for this source was
found in the published notes.

Folland defines averaging on right cosets `xH` using `f(xh)` and left Haar
measure. The existing project quotient is the left quotient `H*x`:
its corresponding averaging formula is `f(h*x)`, and invariance under
replacement of `x` by `h₀*x` requires right invariance of the subgroup
measure. The real-valued restriction, positive-linear packaging, and
compatibility with the published complex integral are derived APIs for
this convention. The proof of continuity above fills in the source's
continuity assertion using a local compact-support argument from pinned
Mathlib. The weaker measure and ambient separation hypotheses are justified
by the implemented proofs, not attributed to additional claims in Folland.
This construction does not prove positive lifting, an averaging-kernel
theorem, or existence of a quotient measure.
