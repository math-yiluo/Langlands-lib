# Cuspidal image of convolution on the positive adelic quotient

`Langlands.TraceFormula.groupSchemeCuspidalImage` proves the universe-polymorphic
[`GroupSchemeCuspidalImageStatement`](GroupSchemeCuspidalImageStatement.md).
It shows that the Haar-integrated right action of a continuous compactly supported
function with vanishing translated radical integrals takes every vector in the
positive-quotient `L²` space into `fullAEL2CuspidalSubmodule`.

## Period unfolding

Fix a proper rational parabolic, write `N` for its adelic radical, and let
`Λ` be its rational subgroup, viewed in `N` and in the ambient adelic group `A`.
The proof begins with a continuous `L²` representative `φ` on the positive
rational quotient. Its pullback `Φ` to `A` is invariant under left multiplication
by `Λ`. For a fixed period argument `x`, substitute `b = n x a` in
`∫ f(a) Φ(n x a) da` using left invariance of Haar measure. The discrete quotient
integration theorem `LeftCosetSpace.integral_eq_integral_automorphize` folds the
new `b` integral onto `Λ \ A`. Its integrand at the cosets of `n` and `b` is

\[
K(\Lambda n,\Lambda b) = \left(\sum_{\delta\in\Lambda}
      f((n x)^{-1}\delta b)\right)\Phi(b).
\]

The identity automorphism in `twistedQuotientKernel` gives the continuity and
support laws for this orbit sum. A compact set `D` of lifts of `Λ \ N` exists by
`leftQuotient_exists_isCompact_image`. The kernel is supported on the product
of `Λ \ N` and the compact image of `D x tsupport f` in `Λ \ A`. Joint
continuity and this compact support prove product integrability and justify
Fubini. Each resulting column integral over `Λ \ N` unfolds by the same
discrete quotient integration theorem, with the lattice index inverted. It
becomes `Φ(b) · ∫ f(x⁻¹ n⁻¹ b) dn`. Right invariance of radical Haar follows
from `haar_isMulRightInvariant_of_compactRationalQuotient`. Haar inversion
invariance then gives zero by the vanishing hypothesis. The quotient in this
calculation is exactly `properParabolicQuotientMeasure` because
`LeftCosetSpace.quotientMeasure_smul` applies the same normalization factor to
radical Haar and to its discrete quotient.

## Passage to `L²`

`integratedTranslationPointwise` and `coeFn_quotientL2RightTranslate` identify
the integrated action almost everywhere with the convolution of the continuous
input. This convolution is continuous by `continuousOn_integral_of_compact_support`,
using the fixed support of `f` in the Haar variable. Measure preservation of
right translation and `Measure.ae_ae_comm` justify evaluating the chosen
continuous input in the integral. The resulting representative has an integrable,
zero period at every norm-one argument by the unfolding calculation.
`mem_aeParabolicCuspidalFunctionSubmodule_congr` transfers the convergence and
vanishing to the `L²` class. Finally, compactly supported continuous functions
approximate arbitrary `L²` vectors by
`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`. The operator is continuous
and `fullAEL2CuspidalClosedSubmodule` is closed, so the result holds on all
of `L²`.

## Source

The changes of variables and the two uses of discrete quotient integration
implement the unfolding in Getz–Hahn, Definition 16.4.1 and Lemma 16.4.2 with
its proof, printed p. 430 (PDF p. 438). Their local supercuspidality produces
the inner adelic vanishing. Here the target supplies that vanishing directly.
The compact support argument and the passage by density use the Library's
continuous test functions on the full adelic group and its almost-everywhere
cuspidal subspace. The registered source is
`getz-hahn-2024-automorphic-representations`, with PDF SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
[Getz–Hahn, *An Introduction to Automorphic Representations* (2024)](https://doi.org/10.1007/978-3-031-41153-3)
