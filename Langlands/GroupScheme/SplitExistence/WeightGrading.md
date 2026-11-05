# The weight grading of square matrices (`WeightGrading`)

Author: Worker 239.

Fix weights `wt : ι → X` for the basis vectors of `R^ι`, with values in an additive group `X`.
This module sets up the bookkeeping used to track how matrices move weights. Later modules
apply it to root operators and to Weyl elements.

## Definitions

- `MapsWt wt f A`: the matrix `A` maps weights by `f : X → X`, that is, every nonzero entry
  `A c d` has `wt c = f (wt d)`.
- `IsWtHom wt μ A`: the matrix `A` is homogeneous of weight `μ`, that is, every nonzero entry
  `A c d` has `wt c = wt d + μ`.
- `wtProj wt μ : Matrix ι ι R →+ Matrix ι ι R` (assuming `DecidableEq X`): the weight-`μ`
  component, which keeps the entries with `wt c = wt d + μ` and replaces the others by `0`.

## Results

- `MapsWt.mul`, `MapsWt.one`: products compose the weight maps, and `1` maps weights by `id`.
- `IsWtHom.zero`, `add`, `neg`, `sub`, `smul`, `sum`: the matrices of a fixed weight form a
  submodule.
- `IsWtHom.mapsWt`, `MapsWt.isWtHom`: being of weight `μ` is the same as mapping weights by
  `· + μ`.
- `IsWtHom.mul`, `IsWtHom.mul'`, `IsWtHom.commutator`: products and commutators add weights.
- `IsWtHom.conj`: if `g` maps weights by an additive map `f`, `g'` maps weights by `f'`, and
  `f (f' x) = x` for all `x`, then `g A g'` has weight `f μ` whenever `A` has weight `μ`.
- `IsWtHom.eq_of_ne_zero`: a nonzero matrix has at most one weight.
- `IsWtHom.map`, `IsWtHom.of_map`, `MapsWt.map`, `MapsWt.of_map`: both notions are preserved
  by applying a ring homomorphism entrywise. They are reflected when the homomorphism is
  injective.
- `IsWtHom.diagonal_commutator`: for an additive character `χ : X →+ R` and `A` of weight `μ`,
  `diag(χ ∘ wt) A − A diag(χ ∘ wt) = χ μ • A`.
- `wtProj_apply`, `wtProj_smul`, `isWtHom_wtProj`, `IsWtHom.wtProj_self`,
  `IsWtHom.wtProj_ne`: `wtProj μ A` has weight `μ`. It fixes matrices of weight `μ` and kills
  matrices of any other weight.

Each proof is an entrywise computation with `Matrix.mul_apply` and a sum in which every
nonzero term satisfies the weight equation.

## Provenance

This is the elementary bookkeeping behind weight-space decompositions (Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §§8 and 20). The formulation for
matrices with weighted basis vectors is internal to this project.
