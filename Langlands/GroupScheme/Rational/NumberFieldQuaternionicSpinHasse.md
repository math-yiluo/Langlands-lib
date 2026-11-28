# The Hasse kernel for quaternionic spin groups over number fields

`Langlands.GroupScheme.numberFieldQuaternionicSpinHasse` proves
`NumberFieldQuaternionicSpinHasseStatement` in every universe. Let `F` be a number field,
`D` a central quaternion division algebra over `F`, and `σ` a first-kind involution of `D`
with symmetric subspace of dimension three. Let `q : σ.QuadraticForms (Fin n)` be
nondegenerate with `4 ≤ n`, and let `π : G ⟶ σ.isometryGroup q` satisfy `σ.IsSpinCover q π`.
For a finite Galois extension `L/F`, a cocycle of `G` on `GaloisCocycle.cover F L` is a
coboundary on this cover if it is trivial on the full pullback cover over every completion.

This is the finite-cover formulation of the trivial-fiber part of the spin Hasse
principle for skew-hermitian forms over quaternion division algebras in Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), §5.10, printed pp. 95–98.
The central cover onto the special unitary group appears in §5.11, sequence (4),
printed p. 101.

## Proof

The Lean proof applies `numberFieldQuaternionicSpinHasse_of_kernels` with
`numberFieldQuaternionicNormOneIsometryHasse` and
`numberFieldQuaternionicSpinKernelHasse`. The reduction identifies the identity
component of the isometry group with its reduced-norm-one subgroup. The first input
trivializes the projected cocycle in this subgroup. The reduction then lifts its
trivializing point after a finite Galois refinement and twists the refined cocycle
into the scheme kernel of `π`. The second input trivializes the image of that kernel
cocycle in `G`. Undoing the twist and descending along the refinement gives a
coboundary on the original cover.
