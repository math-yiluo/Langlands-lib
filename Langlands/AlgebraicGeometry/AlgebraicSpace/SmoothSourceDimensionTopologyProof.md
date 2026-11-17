# Rational-point topology of the actual smooth dimension decomposition: proof

Author: Worker 437.

`Langlands.AlgebraicGeometry.AlgebraicSpace.smoothSourceDimensionTopology` proves the
published proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionTopologyStatement`
(`SmoothSourceDimensionTopologyStatement.lean`) in every universe `u`.

## What is proved

Let `K` be a nontrivially normed field with `IsHenselianValuedField K`, let `X` be an
algebraic space over `Spec K` with `hX : SmoothOverBase X`, and assume
`IsQuasiSeparated X`. Give `X(K)` = `RingPoints K X K` the topology
`etaleChartTopology K X`. Give each dimension piece's `K`-points
`RingPoints K (SmoothDimensionPieces.space hX n) K` its own `etaleChartTopology`. Give the
dependent sum over all `n : ℕ` Mathlib's disjoint-union (Sigma) topology. Then the published
equivalence `SmoothDimensionPieces.fieldPointEquiv hX` is a homeomorphism (`IsHomeomorph`).
No completeness, local or global separatedness, finite range, quasi-compactness, positive
dimension or nonempty point set is assumed. Empty pieces and dimension zero are included.

## Implemented proof

The proof shows that the inverse equivalence is continuous and open, summand by summand.
By the published formula `fieldPointEquiv_symm_apply`, the inverse restricted to summand
`n` is the actual point map `RingPoints.map (inclusion hX n)`; this holds definitionally,
and the proof uses it without rewriting.

1. `X` satisfies `IsQuasiSeparatedLocallyFiniteType K X`. Quasi-separatedness is the
   hypothesis. Local finite type is `SmoothOverBase.locallyOfFiniteType`
   (`StructuralAtlasGeometry`).
2. For each `n`, the piece `space hX n` satisfies the same condition. Quasi-separatedness
   is `SmoothDimensionPieces.space_isQuasiSeparated`. Local finite type comes from
   `SmoothDimensionPieces.space_smoothOverBase` and `SmoothOverBase.locallyOfFiniteType`
   (`SmoothSourceDimensionPieces`).
3. `SmoothDimensionPieces.inclusion_isOpenImmersion` says the actual inclusion
   `inclusion hX n : space hX n ⟶ X` is a genuine open immersion. The published
   `isOpenEmbedding_ringPointsMap` (`EtaleChartTopologyFunctorial`) applies over the
   henselian field `K`. So `RingPoints.map (inclusion hX n)` is an open embedding for the
   two étale-chart topologies. This holds for every `n`, including empty pieces.
4. Let `e := SmoothDimensionPieces.fieldPointEquiv hX` (with `L := K`). Mathlib's
   `continuous_sigma` shows `e.symm` is continuous, because each summand restriction is
   continuous by step 3. Mathlib's `isOpenMap_sigma` shows `e.symm` is an open map,
   because each summand restriction is open by step 3.
5. `Equiv.toHomeomorphOfContinuousOpen` turns `e.symm` into a homeomorphism from the Sigma
   space to `X(K)`. Its inverse homeomorphism has underlying function `e`, so
   `Homeomorph.isHomeomorph` gives the statement's `IsHomeomorph` claim.

Steps 1–5 use only published Library results and Mathlib. No analytic atlas, local
separatedness, or étale local inverse is needed.

The development check in the pinned environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
reported no errors and no warnings. The theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source and provenance

The statement is a derived bridge for the varying-dimension clause of Proposition 5.4 in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011.
The source is registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The relevant passages
are printed p.15, Proposition 5.4, and printed p.16, the final paragraph of its proof.
Conrad does not state this dependent-sum homeomorphism separately. The route above is
the open-immersion argument proposed in the task, not a transcription of a printed
proof. Analytic assembly, functoriality across dimension pieces, étale local analytic
inverses, scheme agreement and uniqueness are not proved here.
