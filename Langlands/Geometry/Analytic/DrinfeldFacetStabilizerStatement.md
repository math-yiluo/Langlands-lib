# Statement: the elements of a facet stabilizer with `|det| = 1` form a compact open set

Author: Worker 21.

This module states, without proof, that for a facet `f` of the building of
`GL_{d+1}(F)` the elements of the stabilizer of `f` whose determinant has
absolute value one form a compact open subset of `GL_{d+1}(F)`. The statement
is `Langlands.Analytic.DrinfeldUpperHalfSpace.FacetStabilizerCompactOpenStatement`,
a `Prop`-valued definition. Nothing in the module proves it.

## Statement

For every nontrivially normed field `F` with `ProperSpace F`, every `d : ℕ`
and every set `S` of norm classes on `F^{d+1}` with `NormClass.IsFacet S`, let
`T` be the set of `γ ∈ GL_{d+1}(F)` with `γ ∈ facetStabilizer S` and
`‖det γ‖ = 1`. Then `T` is compact and `T` is open in `GL_{d+1}(F)`.

The ingredients are the published definitions of `DrinfeldReduction` and
`DrinfeldBuildingCovering`:

- `NormClass F (Fin (d + 1) → F)` is the set of homothety classes of
  `VectorNorm`s on `F^{d+1}`. A `VectorNorm` is an ultrametric norm `ν` with
  `ν(t x) = ‖t‖ ν(x)`, positive away from `0`.
- `NormClass.IsFacet S` says that `S` is the set of classes of a chain of
  lattice norms `ν_0 ≤ ν_1 ≤ ⋯ ≤ ν_k` with `‖t‖ ν_k ≤ ν_0` for every scalar
  `‖t‖ < 1`. A lattice norm takes its values in `{‖t‖ : t ∈ F}`. In terms of
  lattices this is a chain `L_0 ⊇ L_1 ⊇ ⋯ ⊇ L_k ⊇ t L_0` for all `‖t‖ < 1`, so
  `S` is the vertex set of a facet of the building.
- `facetStabilizer S` is the stabilizer of the set `S` under the action of
  `GL_{d+1}(F)` on norm classes, `(γ • ν)(a) = ν(a γ)` for row vectors `a`. Its
  elements may permute the vertices of `S`.
- `GL_{d+1}(F)` is Mathlib's `Matrix.GeneralLinearGroup (Fin (d + 1)) F`, the
  units of the matrix ring. Its topology is the units topology, induced by
  `γ ↦ (γ, γ⁻¹)` from the product topology on matrices.

The set `T` is written out as a set, not as a subgroup, so the module needs
only `DrinfeldBuildingCovering`.

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, §2,
printed pp.303–304 (PDF page = printed page − 298):

> Recall that the action of G_J on Ω lifts to an action on ℳ_N, and U(ê) is
> stabilized by a compact open subgroup S(ê) ⊂ G_J. That S(ê) is compact was
> not stated explicitly in [H1], but it follows from the fact that S(ê)
> stabilizes a facet of the building BT and is contained in the kernel of
> g ↦ |χ(g)| where χ is any algebraic character of G_J and | · | is the p-adic
> absolute value.

On printed p.303 (first display), Harris's group is the product
`G_J = (∏_j B(F_j)^×) × ℚ_p^×`, where `F = F_1` and `B(F)` is the matrix
algebra.

## Derived content

The statement is the analogue of Harris's argument for the matrix factor
`B(F)^× = GL_{d+1}(F)` of `G_J`. It is not a statement about `G_J` or `S(ê)`,
neither of which is constructed in the Library.

1. The facets are those of the Library's building of norm classes of
   `F^{d+1}`, not of the building of `G_J^ad`.
2. The algebraic characters of `GL_{d+1}` over `F` are the integer powers of
   `det`. So the elements in the kernel of every `g ↦ |χ(g)|` are those with
   `|det g| = 1`, and `T` is the set of elements of the stabilizer of `f` in
   this kernel. The condition `‖det γ‖ = 1` uses the norm of `F`. It does not
   change if the norm is replaced by a positive power of itself.
3. Harris asserts compactness, and that `S(ê)` is open. The statement asserts
   both properties for `T`.

## Hypotheses

The statement assumes only that `F` is a nontrivially normed field with
`ProperSpace F`, without an ultrametric hypothesis. If `F` is not
ultrametric, then `‖n‖ > 1` for some natural number `n`. For a `VectorNorm`
`ν` this gives `‖n‖ ν(x) = ν(n x) ≤ ν(x)`, so `ν(x) = 0` for every `x`, which
is impossible for `x ≠ 0`. So `F^{d+1}` has no `VectorNorm`s, no set of norm
classes is a facet, and the statement holds vacuously. For ultrametric `F`,
`ProperSpace F` makes `F` a nonarchimedean local field.

## How it is expected to be proved

A proof is not part of this module. One route, for a facet given by a chain
`L_0 ⊇ ⋯ ⊇ L_k`:

- If `γ` fixes the class of `L_i` and `|det γ| = 1`, then `L_i γ⁻¹ = c L_i`
  with `|c|^{d+1} = |det γ|^{-1} = 1`. So `c` is a unit and `L_i γ = L_i`.
  Hence the elements of `T` that fix every vertex of `S` form the group
  `P = ⋂_i GL(L_i)`, where `GL(L)` is the stabilizer of the lattice `L`.
- Each `GL(L)` is a compact open subgroup of `GL_{d+1}(F)`, because it is
  conjugate to `GL_{d+1}(O_F)`. So `P` is a compact open subgroup.
- `T` permutes the finite set `S`, and `P` is the kernel of the resulting
  homomorphism from `T` to the permutations of `S`. So `T` is a finite union
  of cosets `γP`, each of them compact and open.
