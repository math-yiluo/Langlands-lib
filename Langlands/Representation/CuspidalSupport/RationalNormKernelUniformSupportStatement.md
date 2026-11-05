# Uniform fixed-level coefficient support on the actual norm kernel

This is a derived prerequisite extracted from the proof of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VI.3.4, printed pp.145–146 / PDF pp.151–152, especially the
common coefficient space on printed p.146. Its source route uses VI.2.3's
following remark and VI.2.4, printed pp.140–142 / PDF pp.146–148, together
with VI.2.1(b) implies (c). Source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 485 read the original VI.3.4 and VI.2.3–VI.2.4 pages used to isolate
this obligation. The statement supplies no proof of uniform support.

`Langlands.CuspidalSupport.RationalNormKernelUniformSupportStatement` has
exactly the structural telescope of the published
`RationalNormKernelFixedLevelFinitenessStatement`: arbitrary local field
`F : Type uF`, connected reductive group scheme, actual maximal split
torus morphism and generic cocharacter, canonical point topology, local
compactness, `NonarchimedeanGroup`, Hausdorffness, the standard-cocharacter
statement, relative-root-system realization and closed standard unipotent
point subgroups. Field and representation universes remain independent.
Characteristic, rank zero and empty root systems are unrestricted.

The subgroup is the actual `Plancherel.rationalCommonNormKernel G`, with
its inherited topology. For each compact open subgroup `K` of that kernel,
the conclusion is the imported
`CompactCoefficientClass.HasUniformFixedLevelCoefficientSupport K.toSubgroup`.
Thus one compact subset of the kernel contains all inverse coefficients of
all its actual compact irreducible smooth complex representations at that
level, for every actual fixed vector and every invariant algebraic-dual
functional. The compact set precedes all representation and vector choices.

This formulation records the uniformity needed for the source's common
finite-dimensional space. Renard first obtains an ambient coefficient bound
modulo the centre from VI.2.4; converting it to this conclusion must prove
ambient extension, actual fixed-vector and smooth-dual transports, and the
uniform compact-support comparison on the kernel. A compact open subgroup
of the kernel must be carried through its actual inclusion into the ambient
point group, using the kernel's openness, before applying an ambient theorem.
Those are proof obligations, not assumptions hidden in this proposition.

No ambient extension, admissibility, finite restriction family, support bound,
finiteness or category decomposition is a premise. The statement does not use
the determinant-unit product-Levi finiteness theorem. Its proof is a separate
substantial prerequisite for the current fixed-level task, and would still
leave the generic common-support finiteness argument to apply. Norm-kernel
category decomposition remains a separate obligation.
