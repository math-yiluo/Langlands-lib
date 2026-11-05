# Open root generation from actual ordered root products

Author: Worker 1605.

`OpenRootGenerationFromOrderedProducts.{u}` is an internal proposition asserting
the implication from the published `DynamicRootOrderedProductStatement.{u}` to
the published `OpenRootCentralizerGenerationStatement.{u}`.
`openRootCentralizerGeneration_of_dynamicRootOrderedProduct` proves this
implication at arbitrary universe `u`. It does not establish its structural
premise or the unconditional corollary.

The conclusion retains every field, connected reductive group, maximal split
torus and closed centralizer representative quantified by the target. It uses
the canonical `rationalPointTopology` on `G(F)` and `Z(F)` and the subspace
topology on each actual root group. The family `V` remains indexed by all
actual relative roots, including divisible roots. The generated subgroup is
exactly the image of `Z'` joined with the supremum of this whole family.

The first private lemma, `exists_open_restrict_represented`, extends an open
identity neighborhood `W` in a closed subgroup representative `U(F)` to an
ambient open identity neighborhood `C` in `G(F)`. The published embedding
theorem `isEmbedding_rationalPointMap` supplies `W` as the inverse image of
`C`; representability then lifts every point of `C` in the actual subgroup to
a point of `W`. Closedness makes `U` affine, so both point topologies in that
embedding theorem are exactly the named canonical topologies.

The second private lemma, `isOpen_of_dynamic_neighborhoods`, applies
`Dynamic.opposite_cell_mem_nhds_one` to three ambient open identity
neighborhoods controlling the opposite radical, centralizer and positive
radical. That Library theorem uses `rationalSchemeTopology`. For the affine
ambient group, `rationalPointTopology_eq_rationalSchemeTopology` rewrites it
to the canonical topology before the neighborhoods are supplied. There is no
other chart-topology comparison in this module. The resulting product
neighborhood lies in `K` by subgroup multiplication; the canonical rational
points form a topological group, so `K.isOpen_of_mem_nhds` proves openness.
The local-field Hausdorff instance used here is
`Langlands.BruhatTits.localField_t2Space`.

The third private lemma,
`openRootCentralizerGeneration_of_unipotent_neighborhoods`, chooses a generic
cocharacter using `IsSplitTorus.exists_genericCocharacter`. The proved
`genericCentralizer` identifies its dynamic centralizer with the actual torus
centralizer. Apply the first lemma to the open subgroup `Z'`; its image is
contained in the generated subgroup `K`. Radical-neighborhood control for the
chosen cocharacter and its negative supplies the other two neighborhoods.
The proof explicitly identifies the negative cocharacter with precomposition
by `Gm.powerHom _ (-1)`, as required by the opposite-cell theorem, and applies
the second lemma. Affineness supplies separatedness and reductivity supplies
smoothness.

The public theorem supplies that radical-neighborhood control from the explicit
ordered-product premise. Finiteness of the actual relative roots, proved by
`IsSplitTorus.finite_relativeRoots`, makes the indivisible positive roots finite
for any cocharacter. `Set.Finite.fin_param` gives an injective enumeration,
including the empty case. The premise supplies a compatible ordered scheme
product of the corresponding full actual root subgroups onto a closed
representative of the dynamic radical.
`exists_open_restrict_orderedProduct`, imported from Worker 384's
`OpenRootGenerationNeighborhoods`, gives the required ambient neighborhood.
It pulls ambient open representatives of the given subspace-open groups back
through the inverse coordinate morphisms. These maps run between affine
schemes, so they are continuous for the canonical point topologies; a finite
intersection is open. Its ordered product formula puts each restricted point
in `K`. No topology on the finite product scheme is needed. Only the
indivisible positive factors are used to build the neighborhood, and each
chosen `V a` already lies in the supremum indexed by all actual roots.

The provenance is an internal deduction of the neighborhood argument for
Kaletha--Prasad, *Bruhat--Tits Theory: A New Approach* (2023), Corollary 8.2.6,
printed p.291 / PDF p.322, registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`. The original structural inputs
are Proposition 2.11.3 (the open cell) and Theorem 2.11.15 (ordered root
products). The 1 November 2024 corrections, registered source
`kaletha-prasad-2024-corrections`, do not alter Corollary 8.2.6. The
local-field specialization and source conventions are documented in the
published `OpenRootGenerationStatement.md`. This module proves the stated
implication from Library interfaces and makes no claim to prove the missing
root-product decomposition.
