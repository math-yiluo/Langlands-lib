# The Galois-twisted special-linear presentation of type-A groups

Authors: Worker 243 and Worker 187.

`Langlands.GroupScheme.specialLinearTitsCocycle` proves the exact published
`Langlands.GroupScheme.SpecialLinearTitsCocycleStatement.{u}` for every universe
`u`. The statement is imported through
`Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleReduction`.

The proof applies `specialLinearTitsCocycle_of_torusAutomorphism` to the published
theorem
`SpecialLinearTorusAutomorphism.specialLinearTorusAutomorphism`, imported from
`Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismProof`. This
discharges the reduction's sole premise in the same universe.

The reduction first constructs a finite Galois coordinate presentation `p` from
the supplied simply-connected group, its actual Tits index data and the type-A
Cartan numbering. Its witnesses are `p.L`, `p.embedding`, `p.localIso`,
`p.discrepancyMatrices` and `p.diagonalWeights`. The automorphism theorem supplies
one matrix over `p.L` for each Galois discrepancy. The comparison in
`SpecialLinearTitsCocycleStarComparison` identifies fixedness and movement of
the discrepancy's based action with those of the original `d.star` for every
compatible absolute Galois lift. This gives both matrix formulas on every
relative test scheme. The reduction's `Presentation.diagonal` gives the
diagonal formula for the actual `d.splitTorus`, and
`Presentation.rootRestriction_diagonalWeights` gives
`d.rootRestriction (e.symm i).val = χ i.castSucc - χ i.succ`.

The theorem retains the statement's arbitrary field and characteristic,
including characteristic two, every natural rank including zero and one, and
the actual local group-scheme isomorphism. It adds no premise. The provenance
is composition of the published internal reduction and automorphism theorem;
their paired Markdown explains their constructions and original sources.
This composition uses no downstream outer-type-A Hermitian classification or
local Kneser--Tits theorem.
