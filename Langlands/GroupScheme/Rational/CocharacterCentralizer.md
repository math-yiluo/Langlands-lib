# Cocharacter centralizers and character kernels

Worker 1107.

These elementary internal lemmas relate the actual character kernel, its
all-test centralizer, and the dynamic centralizer of a cocharacter. They are
derived from the published constructions in
[RootSubgroup](RootSubgroup.md),
[Kernel](../../AbelianScheme/Kernel.md),
[TorusCentralizer](TorusCentralizer.md),
[Lattice](../Torus/Lattice.md), and
[StandardLeviRootTransport](StandardLeviRootTransport.md).
No new external structure theorem is invoked.

`RelativeRoot.cocharacterKernelPoint a zeta hzero x` constructs the canonical
lift of the point `x ≫ zeta` to the actual character kernel whenever
`hzero : zeta ≫ a = 0`. It applies the inverse of `kernelPointsEquiv` to that
point and its zero-composite equation.
`cocharacterKernelPoint_comp_ι` proves that composing the lift with the kernel
inclusion recovers `x ≫ zeta`, by the inverse law of that equivalence.

For any scheme `B`, commutative group scheme `T`, group scheme `G`,
homomorphism `i : T → G`, character `a`, and cocharacter `zeta` with
`zeta ≫ a = 0`,
`RelativeRoot.kernelCentralizer_le_dynamicCentralizer_of_comp_eq_zero`
proves
`RelativeRoot.kernelCentralizer i a ≤
Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)`.
On the product of a test scheme with `Gm`, the universal cocharacter point
maps to the identity under `a`. The published `kernelPointsEquiv` lifts it to
the actual scheme-theoretic kernel. Kernel-centralizer membership then gives
commutation with this universal point, which is precisely dynamic-centralizer
membership. The argument includes every test scheme, including nonreduced and
nonaffine tests, and does not require the character kernel to be smooth.

Over an integral domain `k`,
`RelativeRoot.kernelCentralizer_le_dynamicCentralizer_of_pairing_eq_zero` obtains the same
inclusion from `latticePairing T a zeta = 0`. Injectivity of
`gmEndEquiv k` turns that equality into `zeta ≫ a = 0`, so the preceding lemma
applies. Neither lemma requires a torus, a relative root, an affine group,
reductivity, or a monomorphic inclusion.

Over a field, `normalizerPoint_mem_dynamicCentralizer_iff` assumes that the
scheme morphism underlying `i` is monomorphic. For every
`n : normalizerPoints i`, it identifies membership of `n` in the dynamic
centralizer of `zeta ≫ i` at the base scheme with
`cocharacterAut (normalizingAut i n) zeta = zeta`.
The right side is the actual morphism equality
`zeta ≫ (normalizingAut i n).hom = zeta`.
The proof uses the existing identification of the dynamic centralizer with
the all-test `Gm` centralizer, its base-point conjugation criterion, and
`groupHom_cocharacterAut_comp`. Equality after inclusion in `G` then cancels
the monomorphism `i` on every test scheme. The converse is direct substitution.
There is no splitness, maximality, or reductivity assumption.

These lemmas supply elementary inputs for relative Weyl and standard-Levi
arguments. They do not establish root reflections, a Coxeter presentation,
standard-cocharacter existence, or a structural comparison theorem.

The integral-domain pairing lemma is named
`kernelCentralizer_le_dynamicCentralizer_of_pairing_eq_zero`; the older
field-specialized `kernelCentralizer_le_dynamicCentralizer` in
`RelativeWeylCoxeterAssembly` retains its original implicit character arguments.
