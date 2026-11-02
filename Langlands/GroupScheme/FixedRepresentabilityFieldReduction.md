# Field reductions for fixed-subgroup representability

This internal construction supplies the field hypotheses of the published
general fixed-subgroup target and proves two conditional reductions. It does
not prove the general representability target.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), Proposition A.8.10(1) and the following remarks, printed pp. 547–549
(PDF pp. 573–575), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The reductions make explicit the field specialization described in the
published statement module.

`fieldCoordinateProjectiveWitness` returns the identity field extension,
together with faithful flatness and projectivity of the base-changed coordinate
module. The latter is a vector space over the field, hence free and projective;
its dimension is unrestricted. The resulting
`hasFpqcProjectiveCoordinateModule_field` holds for every group scheme over the
field, without requiring affineness. `flat_field` uses the fact that every
scheme over a field is flat.

`fieldFixedSubgroupRepresentability_of_general` applies the general target
using this witness, flatness, and the published `fieldSeparated` theorem.
`fieldCentralizerRepresentability_of_fixed` applies the field fixed-subgroup
target to the actual conjugation action and rewrites its fixed functor using
the published `conjugation_fixedSubgroup_eq_torusCentralizer` equality.

Both implications retain arbitrary universe, characteristic, and group schemes.
No finite type or smoothness premise is introduced, and the conclusions are
the unchanged all-test closed-representability predicates.
