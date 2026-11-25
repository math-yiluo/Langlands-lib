# Geometric evaluation of morphisms from finite étale schemes

Module
`Langlands.GroupScheme.Trigonalizable.FiniteEtaleMorphisms`.

For a field extension `L/k`, `EtaleExtensionSplit.geometricTest k L` is
`Spec L` over `Spec k` using the given algebra map. The morphism
`conjugationTest σ` is induced contravariantly by the `k`-automorphism
`σ` of `L`. The proof uses affine spectrum duality in `Over (Spec k)`:
with the chosen affine-spectrum isomorphisms, points correspond to
coordinate algebra maps into `L`, and precomposition by
`conjugationTest σ` corresponds to postcomposition of the coordinate
map by `σ`. Postcomposition of a point by a scheme morphism corresponds
to precomposition by the induced coordinate map.

For `L` separably closed, `geometric_hom_ext` tests equality of two
morphisms `X ⟶ Y` on all `L`-points of `X` when `X` is affine étale over
`k` and `Y` is affine. In addition, when `L/k` is Galois,
`exists_hom_of_equivariant` realizes a function from the `L`-points of `X`
to those of `Y` by an actual `k`-scheme morphism, provided it commutes
with every scalar conjugation. The target need not be étale in either
lemma. `EtaleMultiplicativeTypeOrder.coordinate_etale` supplies the
étale coordinate algebra of `X`; equality and existence of the coordinate
maps are the corresponding [evaluation and descent lemmas](FiniteEtaleEvaluation.md).

These internal adapters connect the coefficient-algebra proof to
[the vector-kernel splitting step](EtaleVectorExtension.md). In that step,
the source of each tested identity is finite étale even though the
extension group serving as target may have positive dimension.
