# Proof of pointed Picard versality descent

Module: `Langlands.AlgebraicGeometry.Picard.ArtinianChartVersalityDescentProof`.

Author: Worker 410, for task `43ead35e-c745-43e8-b3b6-b88e0a294ec9`.

The theorem `artinianChartVersalityDescent.{u}` has exactly the type of the
companion `ArtinianChartVersalityDescentStatement.{u}`. It is the
categorical descent step motivated by Stacks Lemma 98.12.3 (Tag 0CXK),
`artin.pdf`, version ed88ff78, printed pp. 18–19, registered as
`stacks-artin-axioms-approximation-2026-11-06`.

## Implemented proof

`isFormallyVersalAt_of_iso` first transfers versality across an actual
line-bundle isomorphism on the same chart. The published
`PseudofunctorPointFiberObjectIso.mapPoints` changes the family in a fibre
point without changing its map to the chart. Its inverse carries the
given point to the original family, whose versality supplies a lift.
The forward map carries the lift back. The published restriction
coherence and inverse identity prove that its restriction is exactly the
original specified point.

`isFormallyVersalAt_of_pointed_factorization` then treats an actual
pullback family along `i : V → U`. For a lifting problem on `U`, apply the
assumed pointed Artinian factorization to the chart map of the given
point. The resulting map to `V`, together with the inverse of the
published `PseudofunctorPointFiberAtlasRestriction.atlasComparison`,
gives a point of the pullback family over the same test and with the
specified residue map. Versality on `V` lifts that point.
`PseudofunctorPointFiberAtlasRestriction.mapPoints` sends the lift to a
point on `U`. Its published restriction coherence, followed by the
comparison-isomorphism cancellation, proves equality with the original
point, including its full isomorphism data.

The exact target theorem first transfers the hypothesized versality of
`M` across the supplied isomorphism `M ≅ i*L`, then applies this descent
lemma. It needs no injectivity or uniqueness of Artinian factorizations.
The proof reuses the Library's actual relative Picard pseudofunctor and
point-fibre coherence; it assumes no approximation, atlas,
representability, or algebraization proposition.

## Application boundary

This theorem does not construct a completed local chart or prove the
Artinian factorization condition for one. Those algebraic and geometric
inputs remain required in an application of Stacks Lemma 98.12.3. The
approximation and associated graded arguments of Lemma 98.12.7 also
remain separate. The theorem imposes no finiteness, properness,
flatness, or completeness assumptions and preserves universe `u`.
