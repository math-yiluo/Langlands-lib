# Permutation-stable sublattices of invariant lattices

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.Permutation.Lattice`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let a finite group G act on a finite-dimensional real vector space by permuting a basis indexed by a finite type ι. The file shows that every G-stable complete lattice L contains a complete sublattice of finite index with a ℤ-basis that G permutes exactly as it permutes the real basis. Any number of orbits is allowed.

## Main definitions and results

- `coordinatePermutation σ` is the linear automorphism of `ι → ℝ` with `(σ·x) i = x (σ⁻¹ i)`; it sends the standard basis vector at `i` to the one at `σ i`. `permutationRepresentation ρ g` is this map for `ρ : G →* Equiv.Perm ι`.
- `latticeApproximation L x` is a point a of L with x − a in the fundamental parallelepiped of `IsZLattice.basis L`; every coordinate of x − a has absolute value at most `latticeApproximationRadius L`, the sum of the norms of that basis.
- `averagedLatticeVector ρ L hL t i` sums over g ∈ G the g-translates of the approximations of `t • Pi.single ((ρ g).symm i) 1`. `permutationSublattice ρ L hL` is the ℤ-span of these vectors at the scale `permutationLatticeScale L`. It lies in L, is discrete and is a complete lattice (instances), and `permutationSublatticeBasis` is a ℤ-basis with `g · b i = b (ρ g i)`.
- `exists_complete_permutationSublattice`: for G finite and a ρ-stable complete lattice L in `ι → ℝ`, there is a discrete sublattice L' ≤ L spanning the space over ℝ, with a basis indexed by ι permuted by ρ.
- `exists_complete_permutationSublattice_of_basis`: the same in a normed real space E, for an action `α : G →* (E ≃ₗ[ℝ] E)` and a basis `b` with `α g (b i) = b (ρ g i)`.
- `finite_quotient_of_complete_sublattice`: in a finite-dimensional real normed space, a complete lattice inside another has finite quotient. `permutationSublattice_finite_quotient` applies it to the sublattice above.

## Proof

Averaging over G makes the vectors equivariant (reindex the sum by left multiplication). The scale `(|ι| + 1)·B + 1`, with B the approximation radius, makes the matrix of averaged vectors strictly diagonally dominant by columns, so Mathlib's Gershgorin criterion `det_ne_zero_of_sum_col_lt_diag` gives linear independence. The basis version moves L to coordinates with `b.equivFunL` and back with `ZLattice.comap`. Finite index comes from equality of ℤ-ranks.

## Watch for

- Lattices are ℤ-submodules with Mathlib's `IsZLattice ℝ L` and `DiscreteTopology L`; stability under G is the explicit hypothesis `hL`.
- The approximation bounds use the sup norm of `ι → ℝ`.
- The two existence theorems do not state finite index; that is a separate theorem for the explicit `permutationSublattice` in coordinates.
- The sublattice depends on the basis chosen by `IsZLattice.basis L`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/Permutation/Lattice.lean`: the Lean file is the source byte for byte (SHA-256 `664b24c25f0321459dbf2260e7f7d43be76f24167709803d2eb14fc7bf0714b1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
