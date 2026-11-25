# Actual linear conjugation representations on nonaffine kernels

Let `R` be a commutative ring, `G` any group scheme over `Spec R`, `A` an
`R`-algebra, and `J` an ideal of `A` with the square-zero condition
`[Fact (SmoothLifting.SqZero J)]`. No affineness, separatedness or smoothness
of the target is assumed.

The `NonaffineKernel` module constructs the actual reduction kernel,
its commutative group and module structures, and conjugation by any actual
point as an `A`-linear endomorphism. This module packages those endomorphisms
as an actual linear automorphism representation.

`kernelConjugationLinear_val` gives the underlying point formula
`g*x*g⁻¹`. The identity and multiplication lemmas follow by evaluating on
actual points, then using group identities. `kernelConjugationEnd` packages
these laws as a homomorphism into linear endomorphisms.
`kernelConjugationAut` uses conjugation by the inverse point to construct each
inverse linear map and packages a homomorphism into linear automorphisms.
Its value formula is the original conjugation, and
`kernelConjugationAut_eq_of_reduction_eq` transfers the existing dependence
on only the reducing acting point to the full automorphism.

This is internal derived content for the lifting of homomorphisms from groups
of multiplicative type through nilpotent thickenings. The chart-combination
proof of the `NonaffineKernel` and `SmoothLifting` modules supplies the
nonaffine linearity; this module supplies only the elementary
group-representation packaging described above. It does not assert a flat
scalar-extension isomorphism for kernels or construct the regular coefficient
action on a reduced source group, and it does not prove homomorphism lifting.
