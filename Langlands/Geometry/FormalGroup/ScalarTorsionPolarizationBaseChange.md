# Base change of principal polarizations on scalar-power kernels

For a map \(R \to S\) of coefficient algebras, the scheme pullback
comparison identifies each extended torsion kernel with the pullback
of the original kernel. The additive point functor on the new base
therefore identifies with the original point functor evaluated on
the same test over \(R\). The relative character functor has the
corresponding identification by base change and precomposition with
the kernel comparison.

`TorsionCartierDuality.baseChange` composes these identifications with
the given duality isomorphism on the original test. The inclusion
condition is preserved because inclusions and scalar transitions
commute with the kernel comparison. Evaluation on the new test
gives the same global unit as evaluation of the original pairing
on the corresponding points.

This unit formula preserves antisymmetry and defines
`TorsionPrincipalPolarization.baseChange`. The naturality squares for
actual order endomorphisms and the precomposition law for characters
preserve the full order-antilinearity equation. These constructions
give the coefficient extension of the existing finite-level
polarization condition on affine formal modules.
