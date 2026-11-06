# Additive root maps and rational generation for SL₂

This internal derived construction uses the Library's actual determinant-one group scheme
`SpecialLinear.groupScheme (Fin 2) R` and actual additive group
`VectorGroup.groupScheme R 1`. It constructs upper and lower additive root homomorphisms
and proves that their rational-point images generate the special linear group over every
commutative field, in arbitrary characteristic and universe.

For each pair of distinct binary indices, `rootMap` is the actual group-scheme map whose
matrix on every relative test scheme is the transvection with parameter equal to the sole
additive coordinate. Its construction uses the existing global-sections point equivalences
and Yoneda (`homOfPoints`). `pointsEquiv_rootMap` proves this formula on every test scheme,
without an affineness assumption on the test. `upperMap` uses the position (0,1), and
`lowerMap` uses (1,0).

`rationalMatrixEquiv` identifies the actual rational sections with determinant-one matrices
over the base ring using the canonical global-sections isomorphism for its spectrum.
`exists_rational_rootPoint` proves that every scalar transvection lies in the corresponding
actual root-map image. For fields, `eq_top_of_root_images` transports subgroup membership
through this equivalence and applies Mathlib's `Matrix.SL2.transvection_induction`.
It requires no normality assumption. `root_ranges_sup_eq_top` states the resulting equality
of the join of the two actual image subgroups with the whole rational-point group.

The provenance is internal: explicit elementary matrices and the existing Library point
comparisons, with generation supplied by Mathlib's transvection induction. This is the split
SL₂ rank-one calculation needed in a possible local Kneser–Tits development. It does not
identify either root map as a geometric unipotent radical of an actual parabolic, classify
local rank-one groups, handle SL₂ over noncommutative division algebras, or prove the general
local Kneser–Tits statement. Those obligations remain separate.
