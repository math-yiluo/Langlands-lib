# Finite coefficient subspaces killing actual ideal-cohomology classes

This internal construction gives the coefficient-space part of the
obstruction-killing argument for actual elementary Artinian quotients.
All rings, vector spaces and schemes have arbitrary common universe `u`.

For a field `K`, `K`-modules `H` and `V`, and a finite basis `e` of `H`,
`tensorCoefficients e t` flips `t : H ⊗[K] V` and takes its coordinates
in the right-hand basis `e`. Its values lie in `V`.
`tensorCoefficientSubspace e t` is their `K`-linear span in `V`.
The coefficient module need not itself be finite dimensional.
Empty finite bases are allowed.

`tensorCoefficients_map` shows that a linear map `ψ : V →ₗ[K] V'`
applies to each coefficient. Its proof uses tensor induction, the
pure-tensor coordinate formula, and linearity.
`tensor_map_eq_zero_iff_coefficients` applies the injective flip and
coordinate equivalences to show that `id ⊗ ψ` kills `t` exactly when
`ψ` kills every coefficient. The span universal property gives
`tensor_map_eq_zero_iff_subspace`: this is equivalent to
`tensorCoefficientSubspace e t ≤ ψ.ker`.

`tensorCoefficientSubspace_finrank_le` bounds its dimension by
`Module.finrank K H`: the span of a family indexed by the basis has dimension
at most the basis cardinality. `tensorCoefficientSubspace_basis_independent`
proves that this subspace is independent of the finite basis of `H`.
For each of the two candidate spans, use its quotient map in the preceding
vanishing criterion, then test the same vanishing with the other basis.
The two inclusions give equality.

For an actual proper scheme `f : X → Spec k` and a residue field `K` with
`Algebra k K`, `residueCohomology_finite` proves finiteness of each actual
`H^n(X_K, O_X_K)` over `K`. The actual residue projection is proper by base
change, the actual structure module is quasi-coherent, and its affine sections
are finite over themselves. The published proper coherent cohomology finiteness
theorem therefore applies. This lemma does not require flatness or any
Artinian arrow.

Now assume `Flat f` and `IsProper f`. Let `q : A → B` be an actual elementary
surjection of augmented Artinian tests, `b` a finite basis of its actual
kernel with the descended `K` action, and `e` a finite basis of actual
residue-fibre cohomology in degree `n`.
`cohomologyCoefficientSubspace f q b n e x` is the coefficient subspace
of `idealCohomologyTensorEquiv f q b n x`, using the existing tensor
comparison for the unchanged actual ideal-cohomology class `x`.
`cohomologyCoefficientSubspace_finrank_le` gives its bound by
`dim_K H^n(X_K, O_X_K)`.

For every subspace `W` of the actual kernel,
`cohomology_quotient_eq_zero_iff` proves

`cohomologySemilinearMap f q W n x = 0 ↔ cohomologyCoefficientSubspace f q b n e x ≤ W`.

The proof chooses a finite basis of the actual quotient kernel internally,
using its proved finite dimensionality. Actual tensor naturality identifies
the image of `x` with `id ⊗ kernelLinearMap q W` applied to its tensor.
The target tensor equivalence reflects zero. The generic vanishing criterion
and the independently proved equality `ker (kernelLinearMap q W) = W`
then give the equivalence. No target-basis premise remains in the result.
`cohomology_quotient_coefficientSubspace` specializes to `W` equal to the
coefficient subspace itself, so the actual canonical cohomology image vanishes.

The provenance is internal: these are finite-basis tensor calculations,
proper coherent cohomology finiteness, and the actual elementary-kernel
quotient comparison. No residue-field section or `K`-algebra structure on
`A` is assumed. The generic tensor support is basis independent as stated;
the actual construction retains the supplied ideal tensor comparison `b`.
In degree two, the construction applies to the actual source obstruction
class. Identifying its canonical cohomology image with the actual target
lifting obstruction remains a separate naturality comparison. Formal family
iteration, algebraization and the exact field Picard-stack atlas theorem
also remain further obligations.
