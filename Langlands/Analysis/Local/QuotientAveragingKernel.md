# Zero fiber averages and the ambient Haar integral

Worker 121 proves the exact published proposition
`Langlands.QuotientIntegration.RealAveragingKernelIntegralZero`, with closing
theorem `realAveragingKernelIntegralZero`. The theorem has the original universal
proposition as its type, with no additional hypotheses. It imports Worker 101's
published `realQuotientCompactNormalization` from
`Langlands.Analysis.Local.QuotientPositiveLifting`.

The group is locally compact and Hausdorff, the subgroup is closed, and both
carry the supplied regular two-sided Haar measures and Borel structures. The
function is real, continuous and compactly supported. The conclusion concerns
the actual ambient Bochner integral, assuming that every actual subgroup fiber
integral is zero. There is no countability or quotient-measure assumption.

## Source and convention

Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, second edition
(2015), section 2.6, Theorem 2.51, sufficiency proof, printed page 63 (PDF page
76); the normalizer is Lemma 2.49, printed page 62 (PDF page 75).
Registered source: `folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
PDF pages 74–76 were read for this development. There is no corresponding errata
note in the current public notes.

The project uses left cosets `H*g` and the fiber integral `f(h*g)`, reversing
Folland's convention. The proof adapts Folland's double-integral argument and
uses Mathlib's compact-support Fubini theorem. It does not construct a quotient
measure.

## Implemented argument

Let `f` be the given real compactly supported continuous function and let
`q : G → LeftQuotient H` be the canonical projection. Its support image is
compact by continuity of `q`. The ambient function is integrable by continuity
and compact support, since Haar measure is finite on compact sets. The fiber
functions are likewise integrable: the imported
`integrable_subgroup_mul` theorem pulls compact support back along the closed
embedding `h ↦ h.val*g`. Inverse-fiber functions use the same argument composed
with subgroup inversion. The Fubini steps below use the stronger joint
compact-support property of their two kernels.

Use compact normalization on `q(tsupport f)` with the inverse-image measure
`μH.inv`. Inversion preserves regularity, positivity on open sets and finiteness
on compact sets, and interchanges left and right invariance. Therefore this
measure satisfies every hypothesis of the normalizer proposition. The obtained
function `a` satisfies

`∫ h, a(h⁻¹*g) dμH = 1` on `tsupport f`.

This identity follows from the integral transformation under the measurable
equivalence given by inversion. No equality between `μH.inv` and `μH` is
assumed or needed.

The auxiliary compact-support lemma bounds the support of
`(h,g) ↦ f(h*g) * a(g)` by the compact set

`(H ∩ (tsupport f * (tsupport a)⁻¹)) × tsupport a`,

where the first factor is expressed as a preimage under the closed subgroup
embedding. Indeed, nonvanishing implies `h*g ∈ tsupport f` and
`g ∈ tsupport a`, hence `h = (h*g)*g⁻¹` belongs to that first factor.
The support of `(h,g) ↦ f(g)*a(h⁻¹*g)` is compact by applying the same lemma
with the two functions exchanged and pulling back along inversion in the
subgroup coordinate. Both kernels are continuous.

Mathlib's `integral_integral_swap_of_hasCompactSupport` now gives two legitimate
Fubini swaps for the locally finite supplied measures. Its implementation
restricts each measure to the compact projection of the kernel's support,
proves strong measurability of the continuous compactly supported kernel, and
bounds it on those finite measure restrictions. Thus it establishes product
integrability before using Fubini. No global sigma-finiteness, second
countability, or product Borel-space identification is required.

Left invariance of `μG` gives the intermediate change of variables `g ↦ h*g`:

`∫ g, f(g) (∫ h, a(h⁻¹*g) dμH) dμG`

`= ∫ h, ∫ g, f(g) a(h⁻¹*g) dμG dμH`

`= ∫ h, ∫ g, f(h*g) a(g) dμG dμH`

`= ∫ g, (∫ h, f(h*g) dμH) a(g) dμG = 0`.

The first expression equals the integral of `f`: normalization applies on its
topological support, and `f` vanishes everywhere outside that support.
The final expression is zero by the assumed vanishing of each actual fiber
average. These operations do not obtain the desired conclusion by treating a
nonintegrable function's total integral as zero.

The private lemma `kernel_zero_of_normalization` organizes this calculation as
an implication from the compact-normalization proposition. The closing theorem
discharges that premise using the published normalization proof; normalization
is not an assumption of the final theorem.
