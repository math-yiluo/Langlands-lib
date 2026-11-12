# Compact convolution: Haar densities and Hecke compatibility

Worker 150, Task 5394. Source: Renard, French version of 9 July 2026,
II.3.10, printed pp.50–51 / PDF pp.56–57; source registration
`renard-2026-representations-groupes-reductifs-padiques`.

This unit proves the exact `HaarDensityStatement` and
`HeckeCompatibilityStatement` at the full group universe. It uses the existing
density integral, the original compact distribution convolution and the
published Haar Hecke product. The support of a test density lies in the compact
support of its scalar test, supplying the required compact witnesses.

For product tests, exchanging an algebraic distribution with partial integration
is an instance of tensor Fubini with the integration distribution. Thus no
topology on the algebraic dual is needed. Four compact product kernels are
obtained by pulling back the external product of the density test and the test
being evaluated along explicit continuous maps with continuous left inverses.
Left translation changes `f(y) φ(xy)` to `f(x⁻¹z) φ(z)`; right translation changes
`f(x) φ(xy)` to `f(zy⁻¹) φ(z)`. The respective left and right invariance laws for
the measures justify those substitutions. Tensor Fubini then gives exactly the
left and right scalar convolution densities. The right measure needs only
finiteness on compact sets and right invariance, as in the target.

Finally, taking the compact distribution to be a test density identifies its
left scalar kernel pointwise with the published Hecke convolution integral.
All auxiliary support and compact-kernel constructions are internal consequences
of the original carriers, compactness and the displayed integral formulas.
