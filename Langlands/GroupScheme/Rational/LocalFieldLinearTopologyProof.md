# The canonical local-field rational-point topology is the linear-subgroup topology

`Langlands.GroupScheme.localFieldLinearTopology` proves
`LocalFieldLinearTopologyStatement` with no added hypotheses. It covers
every finite-type affine group scheme `G` over every nonarchimedean
local field `F`, in either characteristic.
[Statement](LocalFieldLinearTopologyStatement.md)

## Source

This is the topology comparison recalled in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, V.2.1, printed p. 104 / PDF p. 110 (registered source
`renard-2026-representations-groupes-reductifs-padiques`). A connected
linear algebraic group over `F` embeds, over `F`, in some `GL_N`. The
induced topology makes its rational points a totally disconnected
topological group, and this topology does not depend on the embedding.
Renard states these facts as a recollection and refers to
T. A. Springer, *Linear algebraic groups* (second edition, 1998), his
reference [42], for proofs. The Lean proof does not follow a written
proof. It derives each clause from point-topology results already in
the Library.

## The implemented proof

The rational points of `G` carry the canonical evaluation topology
`rationalPointTopology F G.X`, which is defined without any choice of
embedding. The instances `IsTopologicalRing F` and
`LocallyCompactSpace F` come from `IsNonarchimedeanLocalField F`.
Hausdorffness of `F` is supplied by `BruhatTits.localField_t2Space`.

1. The topological-group, Hausdorff and local-compactness clauses are
   `rationalPoint_isTopologicalGroup`, `rationalPoint_t2Space` and
   `rationalPoint_locallyCompactSpace` for the canonical topology.
   [Rational-point groups](../../AlgebraicGeometry/PointTopology/RationalPointGroups.md)
2. Total disconnectedness is
   `rationalPoint_totallyDisconnectedSpace_of_localField`. It realizes
   the canonical topology inside a product of copies of the totally
   disconnected field `F`.
   [Rational-point evaluation](../../AlgebraicGeometry/PointTopology/RationalPointEvaluation.md)
3. A closed linear embedding exists by the theorem
   `affineLinearEmbeddingStatement`, which proves
   `AffineLinearEmbeddingStatement` for affine group schemes of finite
   type over any field. Here it is applied to `F`.
   [Affine linear embeddings](../AffineLinearEmbeddingProof.md)
4. Let `ρ : MatrixRepresentation G (Fin N)` be any closed linear
   embedding, so the underlying scheme morphism of `ρ` is a closed
   immersion. The general-linear group scheme
   `GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)` is affine and
   is given its own canonical evaluation topology. Since `F` is
   Hausdorff, `isClosedEmbedding_rationalPointMap` shows that composing
   with `ρ` is a closed embedding between the two canonical rational-point
   topologies.
   [Closed represented subgroups](../../AlgebraicGeometry/PointTopology/RepresentedSubgroup.md)
5. `GeneralLinear.rationalPointsContinuousMulEquiv N F` is a homeomorphism
   from those general-linear rational points onto the matrix group
   `Langlands.GeneralLinear N F`, which has the units topology of the
   matrix ring. As a map it equals `GeneralLinear.rationalPointsEquiv`.
   A homeomorphism is a closed embedding. Composing it with step 4 gives
   the closed embedding asserted in the statement.
   [Matrix point topology](../../Group/GL/AlgebraicPointTopology.md)

Step 4 applies to every closed linear embedding. So for every such `ρ`
the topology induced from the matrices equals the canonical evaluation
topology. This is how the proof makes Renard's independence of the
embedding precise. The axioms used are `propext`, `Classical.choice`
and `Quot.sound`.
