# Closed rational loci over extensions of complete normed fields

This is a derived internal prerequisite for the closedness
part of `HenselianExtensionPointEmbeddingStatement`, rather than a separately
numbered assertion attributed to the literature. It isolates the case of
complete fields and a separated space; the reduction from the full hypotheses
is in `HenselianExtensionClosedReduction`, and the exact final proof is
`henselianExtensionPointEmbedding` in `HenselianExtensionPointEmbeddingProof`.

`CompleteExtensionPointClosedRangeStatement` is a proposition definition. It
quantifies over nontrivially normed fields `K,L : Type u`, a normed `K`-algebra
structure on `L`, and completeness of both fields. It then quantifies over an
actual algebraic space `X` over `Spec K` that is quasi-separated and locally of
finite type, and assumes `IsSeparated X`. Its conclusion is that the image of
`extensionPointMap L X : X(K) → X_L(L)` is closed for the etale-chart topology
over `L` on the actual base change.

The map is the coefficient-extension map, using
`baseChangeRingPointsEquiv.symm` after `RingPoints.changeRing (Algebra.ofId K L)`.
The extension is unrestricted: neither algebraicity nor finite degree,
nonarchimedean norms, local compactness, or perfectness is assumed. The
statement does not separately assume henselianity: complete nontrivially normed
fields satisfy the `completeHenselianValuedField` theorem. Nor does
it separately assume that `K` has closed image in `L`: its isometric image is
complete, hence closed. It asks only for closedness of the range; the embedding
part is supplied separately by the henselian point embedding construction.

This module states the prerequisite and contains no proof. The derived
provenance is the explicit specialization of the closed-image part of
`HenselianExtensionPointEmbeddingStatement` to complete fields and separated
spaces, with redundant hypotheses removed by the two field facts just described.
