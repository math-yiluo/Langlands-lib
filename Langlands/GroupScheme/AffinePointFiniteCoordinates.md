# Finite coordinates on actual affine group-scheme points

Author: Worker 94.

This internal comparison connects the actual group-scheme point carrier to the
published affine algebra-point topology API. Let `R` be a commutative ring,
`G` a group scheme over `Spec R` with affine underlying scheme, and `A` an
`R`-algebra. The coordinate algebra is the published
`PointTopology.AffineCoordinateRing R G.X`: the actual global-section ring,
with its algebra structure determined by the specified structure morphism.

`affinePointsAlgebraHomeomorph` uses the existing
`affineSchemePointEquiv` as its underlying bijection. The lemma
`affineSchemePointEquiv_evaluation` proves that this bijection sends an actual
point to its regular-function values, using the spectrum formula for the
existing equivalence and naturality of the canonical affine isomorphism.
Both continuity proofs then use the universal property of the respective
evaluation topologies. Only a topology on `A` is needed for this homeomorphism.
No alternative group law is transported to algebra points.

If `A` is a topological ring and `a : Fin n → AffineCoordinateRing R G.X`
generates the coordinate algebra over `R`,
`isEmbedding_affinePointFiniteEvaluation` proves that evaluating these
functions embeds the actual point space into `A^n` with its product topology.
If `A` is Hausdorff,
`isClosedEmbedding_affinePointFiniteEvaluation` proves that the image is
closed. These assertions compose the published
`finiteCoordinateEmbedding_proof` and
`finiteCoordinateClosedEmbedding_proof` with the constructed homeomorphism.
They include zero generators and use no finite-presentation hypothesis.

For a structure morphism locally of finite type, the published
`affineCoordinate_finiteType` instance supplies finite type of the coordinate
algebra. `affinePointsLocallyCompactSpace` transports the published
`affineLocalCompactness_proof` over any Hausdorff locally compact topological
coefficient ring. `affinePointsSecondCountableTopology` uses a finite
polynomial presentation, the published polynomial-point homeomorphism and
embedding for a surjective algebra map, and inheritance of second countability
along embeddings. This last assertion assumes second countability of `A`
but does not assume Hausdorffness. Neither assertion needs a topology on `R`
or on the coordinate algebra.

The source construction is Getz–Hahn, *An introduction to automorphic
representations* (2024), §2.2, Theorem 2.2.1 and its proof, printed pp.51–54,
especially presentations (2.7) and (2.8). Registered source
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The relative coefficient-algebra comparison and second-countability consequence
are internal deductions using the published constructions named above.
This unit does not assert second countability or local compactness of a
particular adele ring; those coefficient facts must be supplied when specializing.
Restricted-product descriptions, quotient measures and reduction theory remain
separate obligations.
