# Finite volume of the actual norm-one adelic rational quotient

`Langlands.Global.AdelicGroupPoints.NormOneRationalQuotientFiniteVolumeStatement`
is a proposition target for the finite-volume assertion of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), §2.6, Theorem 2.6.3,
printed p.69. Its scope is every number field F and every smooth connected
finite-type affine group scheme G over F. Reductivity and splitness are not
hypotheses. The Lean assumptions `IsAffine G.X.left` and
`LocallyOfFiniteType G.X.hom` express the affine algebraic-group scope:
affineness makes the structure morphism quasi-compact, so locally finite type
here has the usual finite-type meaning. Smoothness and connectedness are
separate premises, with connectedness referring to the underlying scheme.

The carrier is the existing `NormOneRationalQuotient F G`, the actual left
homogeneous quotient of `normOneSubgroup F G` by `rationalNormOneSubgroup F G`.
The former is the intersection of kernels of all actual F-rational character
norms, using the normalized full idelic absolute value. The latter is the
actual principal image in that group, whose inclusion follows from the
proved product formula. No principal-subgroup normality is assumed.

The measure in the conclusion is precisely the existing
`normOneRationalQuotientHaarMeasure F G` from `AdelicGroupHaarMeasure`.
It is the quotient of the fixed `Measure.haar` on the norm-one adelic group
by counting measure on the principal subgroup, constructed using the Borel
fundamental domain. It is independent of the choice of such a domain, is
nonzero and locally finite, and is regular by the imported results. Its
Haar scale is fixed by that definition; the target does not select a different
finite measure or a probability measure.

The conclusion `IsFiniteMeasure` means that the total measure of the actual
quotient is finite. Together with the already proved nonzeroness this would
give finite positive volume. The proposition adds no analytic right-invariance
premise. Right invariance of norm-one Haar, and hence the invariant-measure
interpretation and full complex Weil compatibility, remain separate analytic
proof obligations. Neither such right invariance nor finite volume is proved
by defining this proposition.

The original theorem's compactness criterion is outside this target. The
function-field extension is also outside it. For a connected reductive group,
the imported split-centre comparison and exact measure-transport results can
later transfer this finiteness to the supplied positive/principal quotient,
when their explicit algebraic premises hold. Identifying that supplied positive
subgroup with the source's A_G still needs its own comparison. This file
asserts no Siegel coverage, compactness, reduction proof, or automorphic-space
realization.

The source's measure interpretation is explained immediately before Theorem
2.6.3 and in §3.6, printed p.90, after Lemma 3.6.4: Haar on G(A_F)^1 and
principal counting induce its quotient measure. The October 2026 author errata,
all five pages checked, changes the quotient notation after Theorem 3.2.3 to
right Haar divided by subgroup right Haar; it makes no change to Theorem
2.6.3. Since the source asserts norm-one unimodularity separately, this
convention does not alter the finite-volume target for the fixed Haar scale.
The source attributes the first assertion to Conrad, Theorem 1.3.6; this file
cites the read Getz–Hahn statement and does not claim an independent reading or
formal reuse of Conrad's proof.

Source records: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
§2.6, (2.19), Theorem 2.6.3, printed pp.68–69, and §3.6, printed p.90;
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
October 2026, Chapter 3 §3.2, p.1.
