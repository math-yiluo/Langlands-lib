# Global analysis of the upper first-block disintegration

This module supplies derived convergence steps in the first-block calculation
of Jacquet, Piatetski-Shapiro and Shalika (1983), §4.9, printed pp.416–418, and
§4.10(2), printed p.419. It builds on the exact rectangle change and the
original real raw-norm profile of the neighboring modules.

Write `a=m 0+1` and `b=m 1+1`, with `a+b=t+1`. Both block sizes
are positive, and the complementary dimensions `j,k` are arbitrary, including
zero. The field has its canonical p-adic topology, valuation and Borel
structures. The field and block-carrier universes remain independent.
`firstBlockUpperGlobalAverage` integrates the actual
`firstBlockUpperCoefficient` over the remaining `j × b` columns. It
retains the supplied scalar Haar product measure and small quotient slice.
The definition alone asserts no convergence.

`firstBlockUpperRowAverage_joint_stronglyMeasurable` uses the continuous smaller JPSS
integrand, the measurable row and column joins and parameter integration.
It retains the radical matrix, the actual small quotient and the remaining
external columns. Continuity of the large Whittaker function and smoothness
of the first block suffice, including for zero supplied functionals.

`firstBlockUpperRowAverage_joint_product_control` assumes original rectangle convergence
almost everywhere on the actual radical/quotient product and integrability
there of the original real raw-norm profile. The local column norm bound
then gives three-variable product integrability. Fubini moves the remaining
columns outside the radical and small quotient integrals only after that
convergence has been established. The radical and small quotient measures
in this lemma may be any S-finite measures; the complex parameter `s`
is arbitrary. The original determinant exponent is
`s-(j+k+1)/2`. The norm majorant is the original real profile before
any rectangle averaging.

`integrable_firstBlock_radical_product_ae` supplies the separate global
measure argument. It starts with any measurable real function `N` on the
block-unipotent quotient, integrable on its determinant slice `d`.
The small quotient measure is sigma-finite and compatible with the specified
small unipotent and general-linear Haar measures. The block, mixed and lower
mixed measures are compatible with their specified subgroup Haar measures.
The supplied radical measure is an S-finite additive Haar measure.
The conclusion is integrability of
`(Z,q) ↦ N(fiberPoint q (lowerRadical Z * g))`
on the actual radical measure times the small quotient measure restricted
to slice `d`, for almost every lower mixed point on slice zero and every
representative `g` of that point.

The proof composes the actual first-block and radical kernels. Their
published measure identities give the composed measure exactly as the
radical integral-cube mass times the block-quotient slice measure.
The cube mass is finite, so the original integrability transfers through
this composition. The kernel integrability criterion gives almost-everywhere
integrability on the composite fibers. Applying it again on each such fiber,
and using both exact representative pushforward formulas, gives separate
small-quotient integrability and integrability of its real norm integral
in `Z`. Joint measurability comes from the continuous actual fiber map.
The product integrability criterion then proves the stated actual product
convergence. The proof works for real `N` of either sign.

These are derived analytic refinements of the cited JPSS calculation, using
the existing exact quotient towers. The module does not yet specialize the
last lemma to the original raw norm, identify its average with the radical
average of the first-block section average, or prove the Laurent identity.
It adds no analytic premise to that target; those final specialization steps
remain to be implemented in its consumer.
