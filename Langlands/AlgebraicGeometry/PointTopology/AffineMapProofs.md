# Quotient and coefficient-map proofs for affine point topologies

Author: Worker 105. Submission preparation and source checks: Worker 135.

Proof of the published `AffineMapProperties` target, derived from Conrad, Proposition 2.1 and Example 2.2,
printed pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The rings `R`, `A`, `B`, `S`, and `T` have independent universes. No topology
is imposed on the base ring or either coordinate algebra. Each topological-ring,
Hausdorff, finite-type, or discrete hypothesis occurs only where the published
target requires it; no finite-presentation or nonzero-ring assumption is added.
The coefficient map has direction `S → T`, and the induced point map has
direction `X(S) → X(T)`. Thus the source coefficient ring is the closed or
open subring of the target, correcting the reversed inclusion in Example 2.2.

The quotient theorem uses the surjective-precomposition helpers of the
finite-coordinate proof module. Coefficient embeddings follow by applying
the coefficient embedding to every evaluation coordinate.

For closed coefficient embeddings, the image consists exactly of points
all of whose values lie in the coefficient map's range. The converse uses
the algebra isomorphism from the source ring onto its range, composed with
the point's codomain restriction to that range. The image is the
intersection of the preimages of the closed coefficient range under all
evaluation maps. No separation hypothesis on either ring is needed.

For open coefficient embeddings and a finite-type coordinate algebra, a
finite generating set suffices to test whether every value lies in the
coefficient range. The inverse image of that range under a point is an
`R`-subalgebra; if it contains the generators, it is the whole coordinate
algebra. The point-map image is therefore a finite intersection of open
evaluation conditions. This argument even works without continuity of ring
operations; the target retains the source's topological-ring hypotheses.

For discreteness, a finite polynomial presentation embeds the point space
in a finite product of the discrete value ring, using the polynomial point
homeomorphism. Embeddings inherit discreteness from their codomain.
The final theorem proves the aggregate `AffineMapProperties` target.

These proofs do not discharge the separate actual scheme closed-immersion,
nonaffine, adelic or algebraic-space obligations.
