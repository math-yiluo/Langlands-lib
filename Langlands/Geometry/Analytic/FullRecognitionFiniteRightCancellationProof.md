# Finite right cancellation over a common open base

`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.finiteOverRightCancellation`
proves `FiniteOverRightCancellationStatement.{u, v, w} K`. Given actual strong
maps `g` and `g'`, the inclusion `g(V) ⊆ U`, and finiteness over the common
open base `T` for `g'` and the saturated composite, the theorem proves
`g.IsFiniteOver V U`. For each recognized affinoid `W` in `U`, this gives a
recognized affinoid with locus `V ∩ g⁻¹(W.locus)` and a finite Banach actual
pullback along `g`. The field, space, and index universes are independent.
The ambient analytic spaces may be non-Hausdorff, and the ground field may
be trivially valued. The presentations allow arbitrary positive finite
polyradii. [Target statement](FullRecognitionFiniteRightCancellationStatement.md)

## Implemented proof

For each `x ∈ U`, finiteness of `g'` gives `g'(x) ∈ T`. The recognized
neighborhood theorem gives a finite family of recognized affinoids `Z`
through `g'(x)` inside `T`, with union a neighborhood of `g'(x)`.
For each `Z`, `finiteCommonBaseTriangle` obtains the recognized middle
and source affinoids from the two finiteness hypotheses. It uses
`g(V) ⊆ U` to identify the source with the full preimage of the middle
in `V`. The triangle identifies the actual bounded pullbacks and applies
`BoundedAlgHom.IsFiniteBanach.of_comp` to prove finiteness of the pullback
from the middle to the source.
[Common-base triangle](FiniteCommonBaseTriangle.md)

Each middle locus is `U ∩ g'⁻¹(Z.locus)` and contains `x`. The proof takes the
finite range of these middle affinoids. Its union contains the intersection
of `U` with the inverse image of the original neighborhood union. This
intersection is a neighborhood of `x` by continuity of `g'` and openness of
`U`. The resulting family satisfies `finiteOverTargetLocality`, which
recognizes the full preimage and proves finiteness of the actual pullback
for every recognized affinoid in `U`.
[Target-locality proof](FullRecognitionFiniteTargetLocalityProof.md)

## Provenance

The cancellation law follows from the common-base triangle construction
and target-locality. The all-affinoid convention for finite morphisms
and the target-locality implication come from Berkovich, *Étale cohomology
for non-Archimedean analytic spaces* (1993), Lemma 1.3.7 and the following
definition, printed pages 27–28 (PDF pages 24–25). The registered source
is `berkovich-1993-etale-cohomology`.
