# Existence of compatible quotient measures

Worker 112 proves `CompatibleMeasureExistsForClosedSubgroups` with the theorem
`Langlands.QuotientIntegration.compatibleMeasureExists`. The target quantifies
exactly the locally compact Hausdorff group, closed subgroup, supplied Borel
structures and regular two-sided Haar measures, and concludes the unchanged
`CompatibleMeasureExists H μG μH`. There is no extra countability or
quotient-measure hypothesis.

The quotient is the existing `LeftQuotient H`, representing cosets `H*g`.
The proof obtains its Hausdorff and locally compact instances from the
published `leftQuotient_t2Space H hH` and
`leftQuotient_locallyCompactSpace H`. These are deductions from the group and
closed-subgroup hypotheses, not additional assumptions.

## The real averaging map and descended functional

Set `P := quotientAverageRealLinear H hH μH`, the actual real subgroup
averaging map on compactly supported continuous functions. Its representative
formula is

`P f (H*g) = ∫ h : H, f(h.val*g) dμH`.

The published `realQuotientPositiveLifting` supplies a preimage of every real
quotient test function and a nonnegative preimage when that test function is
nonnegative. Quotient induction and the representative formula identify these
lifts with preimages under `P`, proving surjectivity and positive lifting for
the linear map itself.

If `P f = 0`, its representative formula says that every fiber integral of
`f` vanishes. Applying the published `realAveragingKernelIntegralZero` then
shows that the ambient integral of `f` is zero. This gives the precise linear
kernel containment required by `measureOfPositiveAveraging`.

The proof defines `ν := measureOfPositiveAveraging μG P hsurj hker hpos`.
This construction descends the actual ambient integration functional through
the kernel of `P`, proves positivity using the positive lifts, and applies
Mathlib's real Riesz representation theorem. In particular, it constructs an
actual measure rather than taking a proposed quotient functional as input.
The imported construction gives regularity and

`∫ q, P f q dν = ∫ g, f g dμG`.

## The five compatibility fields

Since Haar measure `μG` is nonzero and regular, the published
`exists_compact_integral_ne_zero` gives a real compactly supported continuous
function with nonzero ambient integral. The preceding identity shows that
`ν` cannot be zero. Regularity is the Riesz construction's regularity result.

For right invariance, `compactRightTranslate g` sends `f(x)` to `f(x*g)`.
The published `compactAveraging_rightTranslate` proves that this operation
intertwines `P` with the existing quotient homeomorphism `rightTranslate H g`.
The published `integral_compactRightTranslate` uses right invariance of `μG`
to preserve ambient integration. The transfer theorem
`measureOfPositiveAveraging_preserving` therefore makes each quotient right
translation measure preserving. Its underlying argument identifies the
translated regular measure by its integrals against real test functions.

For a continuous compactly supported complex function `f`, the published
`integrable_subgroup_mul_of_hasCompactSupport` gives genuine integrability of
every fiber function. The complexification bridge applies `P` to the real
and imaginary parts and identifies their complex combination with the
existing `quotientAverage H μH f`. It is continuous with compact support, so
it is integrable against the regular measure `ν`. Finally the real Riesz
identity for these two parts gives the exact complex Weil integral formula.
These are respectively `quotientAverage_integrable_of_real` and
`integral_quotientAverage_of_real`. Thus every field of the original
`IsCompatible` is supplied.

## Provenance and scope

This proof assembles the published topology, real averaging, positive lifting,
kernel, functional, translation and complexification results. It introduces
no new definition of cosets, translation, compatibility or subgroup averaging.
All temporary inputs used during development are discharged by the named
proofs above. The result covers arbitrary rank when the group and subgroup
satisfy its hypotheses; particular general-linear and unipotent instances
are separate applications.

The mathematical source is Gerald B. Folland, *A Course in Abstract Harmonic
Analysis*, second edition (2015), section 2.6, Proposition 2.50 and the
sufficiency proof of Theorem 2.51, printed pages 62–63 / PDF pages 75–76.
Registered source: `folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The original pages 74–76 were read. Folland uses `gH` and left translation;
the project uses `H*g` and right translation. The supplied two-sided Haar
measures satisfy the corresponding unimodular specialization. The implemented
functional descent uses the quotient-of-kernel construction and Mathlib
`RealRMK`, and the complex step uses the real and imaginary parts. This module
proves existence with the stated compatibility fields and makes no additional
uniqueness claim.
