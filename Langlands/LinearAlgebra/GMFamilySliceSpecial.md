# Special coarse subspaces and the affine vertex sum

This module extends the affine-slice description of the descent formula from a coarse Levi flat to a special subspace in the sense of Arthur. The data are a root set `R` in a finite-dimensional real inner product space, a Levi flat `a₁`, a subspace `a ⊆ a₁` containing the central space, and the general-position data of `CentralSubspaceDescent.DescentPosition` from [GMFamilyCentralSubspaceVertices](GMFamilyCentralSubspaceVertices.md). The natural expansions of the fine positive roots in the fine simple roots are fixed by `natCoeff`.

`IsSpecialSubspace R a a₁ m` asks for positive weights `m` on the roots and, for every nonzero vector `β` of `a`, that the `m`-weighted sum of the restrictions to `a₁` of the roots whose restriction to `a` is `β` lies in `a`. With the weights equal to multiplicities this is the special-subspace condition of J. Arthur, *The invariant trace formula. I. Local theory* (1988), §7, printed p.355 (PDF p.33), `arthur-1988-invariant-trace-formula-I`: the weighted sum vanishes on the orthogonal complement of `a` in `a₁`.

## Projected simple roots

Fix a coarse chamber `S` and a fine chamber `P` containing its positive roots. Several fine simple roots of `P` may have the same nonzero projection to `a`. `sliceValues` is the finite set of distinct nonzero projections.

- `linearIndependent_sliceValues`. The distinct values are linearly independent. By specialness each value `v` equals `N_v⁻¹ ∑ m_r r|_{a₁}` over its fibre, a nonnegative combination of the fine simple roots with coefficients from the natural expansions of the fine positive roots. A linear relation among the values therefore gives a relation among these coefficient vectors. If a coefficient vector of the value `v'` has a nonzero entry at a fine simple root over `v`, the height of `v'` at a coarse regular point is strictly larger than that of `v`, unless `v' = v`. The abstract lemma `linearIndependent_of_height_triangular` then excludes a nontrivial relation by looking at a value of maximal height.
- `value_mem_simpleRoots`. Every value is a coarse simple root. If it were a sum of two restricted positive roots, the expansions of the two summands in the values, with natural coefficients, would add up to a single value; by independence one summand would have all coefficients zero, hence vanishing restriction, which is impossible for a root positive at a coarse regular point.
- `exists_value_of_mem_simpleRoots`. Every coarse simple root is a value. Choose an ambient regular point whose closed chamber contains the fine regular point, and a root over the coarse simple root of minimal ambient height. It is an ambient simple root: a decomposition into two ambient positive roots either has a summand with zero restriction, giving a lower root over the same vector, or exhibits the coarse simple root as a sum of two restricted positive roots. Its restriction to `a₁` is then a fine simple root of `P` (`simpleRoots_posSet_eq_image`).

Thus the values form a basis of the noncentral coarse space (`sliceValuesBasis`), in bijection with the coarse simple roots (`repSimpleEquiv`).

## The vertex sum

A basis of projected normals contains exactly one index over each value (`basisIndex_exists_mem`, `basisIndex_injOn`). `repOffset` keeps the offsets of the constant inequalities, vanishes on the index of least enumeration over each value, and takes distinct positive values `n + 1` elsewhere. These offsets are regular (`repOffset_regular`), and only the basis of least indices can be feasible (`eq_repBasis_of_feasible`); it is feasible exactly when every constant inequality is strict. Its weight is the reciprocal coarse denominator (`weight_repBasis`). The invariance theorem `vertexSum_eq_of_regular` of the affine vertex sum moves the slice offsets to these offsets without changing the signs of the constant inequalities, which gives `vertexSum_eq_of_special_extension`.

The statement uses the lift predicate `isSliceLift` of [GMFamilyCentralSubspaceChambers](GMFamilyCentralSubspaceChambers.md). The remaining inputs of the descent formula — vanishing for fine chambers over no coarse chamber, the unique selected lift and the uniqueness of the coarse chamber under a fine chamber — are proved there for every coarse subspace containing the central space.

## Source

Arthur 1988, §7 and Appendix, printed pp.355–357 and 378–383 (PDF pp.33–35 and 56–61), `arthur-1988-invariant-trace-formula-I`, SHA-256 `902db792ffe113507165a252b0c1b8c59f78ab8d04def1c5c39b0372362dc3ac`. Arthur proves the descent formula through Fourier transforms of convex polytopes and cites Langlands, *On the functional equations satisfied by Eisenstein series*, Lemma 2.2, for the independence of the simple roots of a special subspace. The proofs here are finite linear-algebra arguments on the Euclidean root arrangement and the affine vertex sum.
