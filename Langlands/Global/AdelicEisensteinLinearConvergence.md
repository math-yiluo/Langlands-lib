# Linear Eisenstein summation with compact majorants

`compactMajorantSections` consists of the scalar functions for which each compact set of adelic points admits one summable norm bound on the Eisenstein terms at the fixed parameter. The triangle inequality and scalar norm law give closure under addition and scalar multiplication. Singletons give pointwise summability, and the usual sum laws make the actual Eisenstein series a linear map on this submodule.

`exists_regular_compactMajorantSections` applies absolute convergence to each member of a finite family of automorphic sections and chooses a common upper bound for their thresholds. At every sufficiently regular parameter the linear span of the family lies in the compact-majorant submodule. This lets a finite holomorphic family of sections be summed linearly on a single convergence region even when its scalar coefficients depend on the parameter.

The definition and the common-threshold lemma are derived from Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*, II.1.5, printed p. 85, and Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, Section 2.2 and equation (2.1), printed p. 191 (PDF p. 5). The norm majorants here are precisely the ones in `EisensteinAbsoluteConvergenceStatement`.
