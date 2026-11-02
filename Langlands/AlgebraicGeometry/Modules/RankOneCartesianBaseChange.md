# Rank-one loci under arbitrary cartesian base change

This is an internal derivation from the actual-stalk reflection and spreading
constructions in `RankOneStalkReflection` and `RankOneStalkSpreading`, and
Mathlib's stability of flat scheme morphisms under base change.

Let the square with maps `a : P → Y`, `p : P → T`, `f : Y → S`, and
`g : T → S` be cartesian. Assume `f` is locally of finite presentation and
`M` is a locally finitely presented module sheaf on `Y`, relatively flat
over `S`. The construction `stalkRankOneEquivOfCartesianPullback` produces
an actual linear equivalence of the stalk of `M` at `a(x)` with its local
ring from such an equivalence of the ordinary pulled-back module at `x`.

For `s = f(a(x))`, form `T_s = T ×_S Spec κ(s)` and then
`P_s = P ×_T T_s`. Pasting pullback squares identifies this with the
original `S`-residue fibre of `P`. The induced map from `P_s` to the
original residue fibre `Y_s` is a base change of
`T_s → Spec κ(s)`. Every scheme over this field spectrum is flat, so the
induced fibre map is flat. Applying
`stalkRankOneEquivOfFiberwiseFlatPullback` gives the required equivalence.
No compatibility with the supplied basis is asserted.

The lemma `rankOneLocus_pullback_of_isPullback` proves equality between the
rank-one locus of the pulled-back module and the inverse image of the
original rank-one locus. A point in the pulled-back locus gives a
rank-one stalk, which the construction reflects; finite presentation
spreads the resulting original stalk basis to an actual trivializing open
neighbourhood. The other inclusion follows by pulling back local
trivializations.

The construction retains arbitrary universe `u`, arbitrary base-change
schemes, and nonnoetherian bases. It introduces no flatness assumption on
`g` and proves no Picard-stack atlas existence assertion.
