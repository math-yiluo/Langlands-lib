# Common compact support and fixed-level finiteness

This is an internal, derived formulation of the final coefficient-space step in
David Renard, *Représentations des groupes réductifs p-adiques*, French edition
of 9 July 2026, VI.3.4, printed p.146 / PDF p.152, with condition (KF) in IV.1.7,
printed p.95 / PDF p.101. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 485 read those original pages and IV.1.3, printed pp.89–90 / PDF
pp.95–96. This module states a reduction and proves no finiteness theorem.

`Langlands.CompactCoefficientClass.HasUniformFixedLevelCoefficientSupport K`
asserts existence of one compact set `C` in a topological group `G`, chosen
before all actual irreducible compact-coefficient smooth complex
representations `D`, all `K`-fixed vectors `v`, and all algebraic functionals
`ℓ` invariant under `K`. Every inverse coefficient
`g ↦ ℓ (D.obj.representation g⁻¹ v)` has its ordinary function support in `C`.
The field, representation, smooth-dual coefficient condition, actual
isomorphism quotient and fixed-vector submodule are the existing Library
objects. Representation carriers remain in an independent universe `uV`.

If `K` is open, each invariant functional is a smooth dual vector. That is a
consequence to use in a proof, not an extra premise or a modified dual.
The uniformity is over every representation and both coefficient inputs;
compactness separately for each coefficient does not imply this predicate.
The use of inverse coefficients agrees with the imported left-Haar
intertwiner construction. A common support for forward coefficients gives
one for inverse coefficients by inversion, which preserves compactness.

`Langlands.CompactCoefficientClass.UniformSupportFixedLevelFinitenessStatement`
quantifies over an arbitrary topological group, its Borel measurable structure,
a supplied left Haar measure, and a compact open subgroup `K`. It says the
uniform-support predicate implies finiteness of the existing actual set
`fixedStratum K.toSubgroup`. No unimodularity, countability, admissibility,
finite-dimensional fixed spaces, ambient reductive group or category
decomposition is a premise. The statement is an internal generalization of
Renard's finite-dimensional coefficient-space argument, rather than a
verbatim theorem from his unimodular setting. Its proposed proof uses the
published inverse-coefficient separation construction, which needs only left
Haar invariance, and finite evaluation on a compact support modulo an open
subgroup. Those steps remain proof obligations here.

This conditional reduction does not assert that reductive norm kernels have
the required uniform support. In particular it does not prove the separate
`RationalNormKernelFixedLevelFinitenessStatement`.
