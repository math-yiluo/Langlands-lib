# Actual Picard obstruction under an elementary kernel subspace quotient

This internal specialization proves naturality of the actual Picard obstruction
under quotienting an elementary Artinian kernel by a residue-field subspace.
It then gives an actual pointed lift after quotienting by a subspace whose
dimension is bounded by the residue fibre's structure-sheaf H².

Fix a commutative ring `k`, a field `K` with its specified `k`-algebra structure,
a scheme morphism `f : X → Spec k`, and an elementary surjection `q : A → B`
of augmented Artinian tests. The elementary hypothesis is supplied as
`Fact (IsElementarySurjection q)`. The kernel has its existing descended
`K`-module structure. All objects have arbitrary common universe `u`.
For a `K`-linear subspace `W` of the actual kernel, retain the imported actual
quotient test `Q = A/W` and the elementary arrows `π : A → Q`, `r : Q → B`.
There is no chosen section of an augmentation or extra `K`-algebra structure
on either source ring, and zero subspaces and zero kernels are allowed.

Assume `QuasiCompact f`. Let `M` be an actual line bundle on the residue-fibre
scheme and `L` an actual pointed deformation of `M` over `B`. The theorem
`obstruction_quotient` identifies

```text
cohomologySemilinearMap f q W 2 (obstruction f M q L)
  = obstruction f M r L.
```

Both obstructions are the unchanged actual square-zero Picard obstructions,
and the map is the existing quotient map on the unchanged ideal-cohomology
groups. In particular the target is the obstruction of the same pointed
deformation `L`, with its original bundle and residue identification.

The proof applies injectivity of `relativeEquiv` for the target, then cancels
its inverse in the definition of `cohomologySemilinearMap`.
`relativeCohomologyMap_eq` identifies the actual quotient cohomology morphism
with the canonical closed-immersion map. The additional helper
`ArtinianKernelQuotient.idealMap_eq_kernelModuleMap` makes the exact source
kernel transport and actual intermediate structure-kernel map explicit. This
helper first proves the identity for arbitrary schemes, avoiding reduction
of the concrete Artinian quotient objects. Two private reflexive identities
expose the scalar-restriction maps and the actual obstruction classes.
`SquareZeroRelativeObstructionNaturality.obstructionMap_factorization` then
applies to the actual scheme factorization, actual quotient ring map and
projection square. The elementary projection has square-zero kernel, so it
supplies the required nilpotence hypothesis. The elementary source and
reduction supply both square-zero obstruction hypotheses. Quasi-compactness
makes the actual relative source scheme compact. Symmetry of that comparison
gives the desired equality.

For the remaining declarations assume also `Flat f` and `IsProper f`.
Supply finite bases `b` of the actual kernel of `q` and `e` of the actual
residue-fibre structure-sheaf H². The definition
`obstructionCoefficientSubspace` is the existing
`cohomologyCoefficientSubspace` applied to the actual source obstruction,
using those bases and the existing ideal-cohomology tensor comparison.
`obstructionCoefficientSubspace_finrank_le` bounds its `K`-dimension by the
dimension of that H², by the existing coefficient-subspace bound.

The theorem `obstruction_quotient_eq_zero_iff` says the actual target
obstruction vanishes precisely when `W` contains this coefficient subspace.
It rewrites by `obstruction_quotient` and applies the already proved exact
criterion for vanishing under the actual cohomology quotient map.
`pointed_lift_quotient_iff` composes that criterion with
`ArtinianSquareZeroPicardLifting.pointed_lift_iff_obstruction`. Its conclusion
is existence of an actual pointed deformation over `Q` and an isomorphism
from its restriction to the original pointed deformation `L`, including the
specified residue data.

Finally `exists_kernel_subspace_lift` removes the supplied bases from the
conclusion. Elementary-kernel finiteness and proper coherent cohomology
finiteness provide finite-dimensionality of the kernel and residue-fibre H².
The proof chooses their existing free bases, takes the coefficient subspace
of the actual obstruction, invokes its dimension bound, and uses the pointed
lifting criterion with reflexive containment. It produces an actual subspace
`W` with dimension at most that of residue-fibre H², together with the actual
pointed lift over its actual quotient test. Properness already supplies the
quasi-compactness used by this theorem.

The provenance is internal: all maps, obstructions, quotient tests, tensor
comparisons and pointed lifting criteria are imported existing constructions.
The new content is their exact specialization and combination. Formal family
iteration, a complete local hull, effectivity, algebraization, smooth charts
and the exact field Picard-stack atlas remain separate obligations.
