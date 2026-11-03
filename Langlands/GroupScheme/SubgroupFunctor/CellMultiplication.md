# Multiplication from two subgroup sources

`Langlands.GroupScheme.SubgroupFunctor.cellMultiplication iU iP` is the
actual morphism `U.X ⊗ P.X ⟶ G.X` over an arbitrary base scheme, defined
by `(fst ≫ iU.hom.hom) * (snd ≫ iP.hom.hom)` for group-scheme
homomorphisms `iU : U ⟶ G` and `iP : P ⟶ G`. Its definition requires
no subgroup, smoothness, affineness, or dynamic hypotheses.

`lift_cellMultiplication` evaluates this morphism on a pair of maps
`a : T ⟶ U.X` and `b : T ⟶ P.X`: the result is the product of their
images in `G`. The proof uses the product projection laws and naturality
of multiplication on points.

These declarations were moved unchanged from
[OpenCellNormalizer](OpenCellNormalizer.md), which retains the
conditional self-normalization results. The same multiplication map is
used by [OppositeCellMono](../Dynamic/OppositeCellMono.md) for its
monomorphism result. This module contains only their common construction
and its evaluation law.
