# Faithfully flat projections and comparison from dynamic-factor lifts

Author: Worker 1444.

This derived support module works with actual group schemes over `Spec k`,
where `k : Type u` is any field and the universe `u` is arbitrary. The field
may be imperfect and have positive characteristic. Let `G` be smooth,
connected and affine, and let `χ : Gm → G` be a cocharacter. Write `−χ`
for precomposition with `Gm.powerHom (-1)`.

The intrinsic dynamic subgroup functors are `U(−χ)`, `Z(χ)` and `U(χ)`.
All range and containment conditions in this module are conditions on
every test scheme over the base; they are stronger than statements just
about field-valued points.

`isDominant_of_contains_tripleCell` and
`isSchemeTheoreticallyDominant_of_contains_tripleCell` use actual
representatives `iM`, `iZ`, `iU` of these three functors. For any actual
homomorphism `p : D → G`, containment of the three representative range
functors in `range p` implies dominance and scheme-theoretic dominance
of the underlying scheme morphism of `p`. No geometric assumption on `D`
is used for these conclusions, and `p` need not be an immersion.

The proof applies `tripleCellMultiplication_mem` to the test scheme
`M.X × (Z.X × U.X)`. The universal triple product belongs to `range p`,
so there is an actual scheme morphism `a` to `D.X` whose composite with
`p` is the triple-cell multiplication. The published
`isDominant_tripleCellMultiplication` makes this composite dominant;
dominance then passes to `p`. The published
`smoothConnectedAffineGeometry` makes `G` geometrically integral, hence
integral and reduced. Mathlib's reduced-target criterion upgrades
dominance to scheme-theoretic dominance.

`isSchemeTheoreticallyDominant_of_contains_dynamicFactors` removes the
choices of representatives. Its hypotheses are exactly
`U(−χ) ≤ range p`, `Z(χ) ≤ range p`, and `U(χ) ≤ range p`.
The proof constructs the canonical affine representatives and uses their
range equalities.

`projection_geometry_of_contains_dynamicFactors` additionally assumes that
`D` is affine and locally of finite type over `k`. It proves that the
underlying scheme morphism of `p` is flat, surjective, locally of finite
presentation and quasi-compact. The source need not be smooth, reduced or
connected. The proof uses the preceding scheme-theoretic dominance and
the published `DominantHom.flat_surjective`. Local finite type of `D`
implies local finite type of `p`. Smoothness of `G` over a field makes `G`
locally Noetherian, so `p` is locally of finite presentation. Both schemes
are affine, so `p` is affine and therefore quasi-compact.

`comparisonIsoOfDynamicFactors` constructs an actual isomorphism `G ≅ H`
from the following data:

- `D` is affine and locally of finite type over `k`;
- `G` and `H` are smooth, connected and affine over `k`;
- there are actual homomorphisms `p : D → G` and `q : D → H`;
- cocharacters `χG` and `χH` have their respective three intrinsic dynamic
  factors contained in `range p` and `range q`;
- the full kernel range functors agree:
  `range (kernelι p) = range (kernelι q)`.

The projection-geometry theorem makes both maps fppf and quasi-compact.
They satisfy the published `RelativeRoot.IsFppfQuotient` predicate for
the same subgroup functor `range (kernelι p)`. The construction is exactly
the existing `FppfQuotientComparison.iso`: fpqc homomorphism descent
produces a map in each direction, and cancellation through the faithfully
flat covers proves they are inverse. This module reuses that construction.

`comparisonIsoOfDynamicFactors_fac` proves the equation
`p ≫ e.hom = q` for the constructed isomorphism `e`, and the generated
reassociation lemma allows composition with a further map.
`comparisonIsoOfDynamicFactors_unique` says that any actual isomorphism
satisfying this equation equals `e`.
`comparisonIsoOfDynamicFactors_compatible` proves that if `t : T → D`
has composites `iG : T → G` and `iH : T → H`, then
`iG ≫ e.hom = iH`. Here `T` can be any group scheme; in particular this
applies to a common torus that has already been lifted to `D`.

Provenance is internal and derived: the module combines
`Absolute.TripleCellGeneration`, `SmoothConnectedGeometryProof`,
`DominantHomFaithfullyFlat`, canonical affine dynamic representatives,
`FppfQuotientComparison` and Mathlib morphism properties.
No external literature is newly cited.

This conditional comparison does not construct a common graph subgroup,
derive its factor lifts from matching root data, prove equality of its
full kernels, identify `Z(χ)` with a specified maximal torus, or prove
`SplitCommonTorusIsomorphismStatement`. Those obligations remain separate;
the map and kernel hypotheses here are not premises added to that statement.
