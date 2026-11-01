# The `H¹` dimension bound for abelian schemes over a field

Authors: Worker 274 and Worker 921.

This module proves the published proposition
`Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`. The theorem is
`Langlands.AbelianScheme.fieldStructureSheafH1DimensionBound`. For every field `k`, every abelian
scheme `A` over `Spec k` and every `g` with `A.HasRelativeDimension g`, the `k`-module
`(DerivedSections.relativeCohomology A.X.hom 1).obj (structureSheaf A.X.left)` is
finite-dimensional, and its `finrank` is at most `g`.

It contains no `sorry` and no new axioms.

## Proof

The theorem applies `fieldStructureSheafH1DimensionBound_of_dim_of_vanishing` (module
`Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundCech`) to two published Library
proofs:

- `Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim`, which proves
  `FieldSmoothTopologicalKrullDimStatement`: a quasi-compact scheme smooth of relative dimension
  `g` over a field has topological Krull dimension at most `g`;
- `Langlands.AlgebraicGeometry.Modules.noetherianSeparatedQuasicoherentVanishing`, which proves
  `NoetherianSeparatedQuasicoherentVanishingStatement`: on a noetherian separated scheme of
  topological Krull dimension at most `d`, quasi-coherent cohomology vanishes in degrees above `d`.

Together they give `H^{g + 1}(A, 𝒪_A) = 0`. The helper modules turn this vanishing into the bound.
They are listed in reading order:

1. `Langlands.Cohomology.CechCup`: cup products of Čech cochains of sheaves of commutative rings
   on a finite cover, the Leibniz rule, and products `prod` of degree-one cocycles.
2. `Langlands.Cohomology.CechRefine`: the refinement map of Čech cochains along an index map. It
   commutes with the differential and with products. A degree-one cocycle that becomes a
   coboundary after refinement is already a coboundary.
3. `Langlands.AlgebraicGeometry.CechPullback`: pullback of Čech cochains along a morphism of
   schemes and an index map.
4. `Langlands.AlgebraicGeometry.Modules.CechShift`: dimension shifting with an injective
   resolution step `M → I → Q`. Čech cohomology classes that vanish after refinement already
   vanish, in every degree. Derived vanishing `H^{n}(X, M) = 0` gives Čech exactness in degree `n`
   for covers by affine opens with affine finite intersections.
5. `Langlands.AlgebraicGeometry.Modules.CechTheta`: the comparison between degree-one Čech
   cocycles and derived `H¹`. It is additive, `k`-linear, kills coboundaries, and is surjective
   for affine covers.
6. `Langlands.AlgebraicGeometry.CechKunnethStatement` and `Langlands.AlgebraicGeometry.CechKunneth`
   (Worker 921): the Čech Künneth detection statement on the product cover and its proof. It is
   a slant-product functional that detects products of cocycles pulled back from the two
   factors.
7. `Langlands.AlgebraicGeometry.CechPrimitive`: for a group with constant global functions, a
   degree-one class pulled back along the multiplication equals the sum of its pullbacks along
   the two projections, up to a coboundary on a refined cover. This uses the Library's two-axis
   injectivity `FieldTwoAxisH1Injectivity.exists_coboundary_of_axes`.
8. `Langlands.AlgebraicGeometry.CechH1Bound`: the main induction. If `x₁, …, xₙ` in `H¹` are
   linearly independent and represented by cocycles `z₁, …, zₙ`, then `z₁ ⋯ zₙ` is not a Čech
   coboundary. Exactness in degree `g + 1` therefore bounds every independent family by `g`.
   `Module.rank_le` then gives finite dimension and `finrank ≤ g`.
9. `Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundCech`: the instantiation for
   abelian schemes over a field (multiplication, unit axes, constant global functions, a finite
   affine cover with affine intersections, noetherian and separated total space) and the bridge
   from the two published statements.

## Provenance

The route follows the exterior-algebra argument for `H¹(A, 𝒪_A)` of an abelian variety
(registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, (6.12)–(6.15); compare
Mumford, *Abelian Varieties*, §13). Primitive degree-one classes have nonzero products of every
length up to the number of independent classes, and cohomology vanishes above the dimension.
The formalization works with Čech cochains on finite affine covers instead of the Hopf-algebra
structure on all of `H^*(A, 𝒪_A)`. It needs no perfectness of `k`, and finiteness comes from
bounding independent families. Each helper module's Markdown gives its own details.
