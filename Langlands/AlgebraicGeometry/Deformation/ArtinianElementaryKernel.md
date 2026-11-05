# The actual elementary Artinian kernel over its residue field

This internal construction uses the augmented local Artinian tests of
`ArtinianTests`. The field `K` and all test rings have arbitrary common universe
`u`. An elementary arrow `q : A → B` is surjective and satisfies
`maximalIdeal A * ker q = 0`; its kernel may have any dimension, including zero.

`ElementaryKernel.Kernel q` is the actual ideal `ker q`, retaining its additive
group and its existing `A`-module structure. Multiplication in the displayed
zero ideal product proves `maximalIdeal_smul_eq_zero`. Since the augmentation
kernel is the maximal ideal, it lies in the annihilator of this actual module.

`residueAction` descends the ring homomorphism from `A` to additive
endomorphisms of `ker q` through the specified surjective augmentation `A → K`.
Mathlib's ring-homomorphism descent supplies existence and uniqueness.
`residueModule` is the resulting module on the unchanged additive kernel.
`augmentation_smul` proves that restriction along `A → K` is exactly the
original action. No ring or algebra section `K → A` is assumed or constructed.

The identity map of the kernel is consequently semilinear for `A → K`.
The Artinian source ring is noetherian by Mathlib's Hopkins–Levitzki result,
so its actual ideal kernel is finite as an `A`-module. The surjective semilinear
identity then proves `finiteDimensional` over `K`.

This is an internal algebraic prerequisite for finite Picard obstruction
spaces. It does not identify a relative ideal sheaf with residue-fibre
coefficients or assert finiteness of its cohomology, a formal hull, or an atlas.
