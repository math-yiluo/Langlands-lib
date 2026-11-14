# Corrected KP Proposition 13.5.2 on available data

`Langlands.BruhatTits.MaximalProP.availableMaximalProP` proves exactly the
published `AvailableMaximalProPStatement.{u}`, for arbitrary universe `u`.
For every nonarchimedean local field, connected reductive group and KP building
assignment available for that group, it proves all four corrected conclusions:
every facet positive subgroup is open pro-p in the zero subgroup; it is maximal
there exactly at chambers; every maximal open pro-p subgroup arises this way;
and each chamber positive subgroup has its chamber fixer as its normalizer
inside the zero subgroup.

All groups are the original rational-point subgroups, with the canonical point
topology and the characteristic of the actual residue field. In particular, the
positive subgroup is the radical preimage in the neutral integral model, as in
the published statement.

The implemented proof first works with a single datum satisfying its group
axioms. The classification theorems in `AvailableClassification` supply the
first three clauses using the proved local-model pro-p result, actual facet
quotient comparisons and finite-field Sylow/Borel theorems.

For the normalizer clause, choose an apartment chamber from a regular point
of the locally finite affine reflection arrangement and a generic integral
cocharacter of the actual maximal split torus. The theorem
`isProP_chamber_unipotent_factor` supplies pro-p for both signs of this
cocharacter: each factor is the intersection of the compact neutral-model
fixer with the closed actual dynamic unipotent point group, to which the compact
unipotent pro-p theorem applies. The chamber split theorem then proves the
normalizer identity for this apartment chamber. Its proof uses the Iwahori
factorization and the split Tits-system normalizer theorem.

`chamber_normalizer_eq_of_one_apartment_chamber` transports that identity to
every chamber. A zero-subgroup element conjugating the two chamber fixers also
conjugates their positive subgroups, by their largest-pro-p property.
Conjugation preserves the zero subgroup, intersections and normalizers, so
mapping the apartment identity gives precisely the required identity at the
other chamber. This helper retains its explicit factor hypotheses; the datum
theorem discharges both with the actual pro-p theorem.

`maximalProPConclusions_of_groupAxioms` combines these four clauses.
Finally, availability supplies exactly these single-group axioms through
`IsAvailableFor.groupAxioms`. The entry theorem introduces the original field,
group and assignment and applies the datum theorem. There are no further
premises and no universe, rank, splitness or characteristic restrictions.

The source proposition is Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Proposition 13.5.2, printed pp.476–477 / PDF pp.507–508, source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`. The correction of part (1) to
maximality in `G(F)^0` is in the 1 November 2024 corrections, PDF p.49, source ID
`kaletha-prasad-2024-corrections`. The available-data formulation and source
identifications are those of the unchanged `AvailableStatement` pair. The
normalizer proof here follows the split Tits-system route described above.
