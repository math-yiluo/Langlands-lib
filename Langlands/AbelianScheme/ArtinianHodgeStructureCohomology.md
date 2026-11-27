# The function Čech cohomology of the supplied cover

The function cochains of `AffineCechDeRham` and the cochains of the
structure module in `CechResolution.AllSeq` are the same families of
sections over tuple intersections. The scalar actions are induced by
the same structure morphism, and `dCochain_unit` compares the two
alternating sums. The resulting linear equivalence preserves cocycles
and takes boundaries to boundaries.

For a separated morphism \(f : X \to \operatorname{Spec}(R)\) and a
supplied finite affine open cover \(U\) of \(X\), `structureH1Equiv`
identifies the first Čech cohomology of functions on \(U\) with
\(H^1(X,\mathcal O_X)\) as an \(R\)-module. The map from cocycles to
cohomology is surjective by the affine Čech comparison, with kernel
the coboundaries. When \(f\) is proper and \(R\) is Noetherian,
`structureH1_finite` gives finite generation by applying proper
coherent cohomology finiteness to the structure module.

This identifies the function term over an affine base in Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, revision
of 14 March 2021, §2.1.6, equations (2.1.6.5) and (2.1.6.6), printed
p. 135 (PDF p. 163). The retained source is
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
