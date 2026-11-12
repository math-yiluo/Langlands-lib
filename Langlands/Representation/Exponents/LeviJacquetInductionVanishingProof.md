# Renard VI.5.3 (i) for represented parabolics: proof

Author: Worker 4949. Proof of the published statement
`LeviJacquetInductionVanishingStatement` (Renard 2026, VI.5.3, Proposition (i), printed
p.173 / PDF p.179; source `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). Target of task
`fc21c11d-1a31-468d-a90e-fdda36098677`.

`leviJacquetInductionVanishing : LeviJacquetInductionVanishingStatement.{u, v}` applies
the deduction `leviJacquetInductionVanishing_of_geometricLemma` (module
`LeviJacquetCuspidalReduction`, Worker 1781) to the published represented geometric lemma
`representedGeometricLemma : RepresentedGeometricLemmaStatement.{u, v}` (Renard VI.5.1).
The universes and every binder are those of the statement. No further hypothesis is
used.

As in Renard's proof, the geometric lemma filters `r_Q i_P ρ` by pieces
`i ∘ w ∘ r_{M ∩ w⁻¹ Q w}` indexed by double cosets. Under the nonconjugacy hypothesis,
each source intersection parabolic of `M` is proper. Supercuspidality then kills each
piece, so the filtered module vanishes. The details are in `LeviJacquetCuspidalReduction`.
