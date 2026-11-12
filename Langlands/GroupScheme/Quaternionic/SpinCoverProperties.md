# Almost simplicity and split rank of quaternionic spin covers

This internal derived module is work of Worker 97 for Task 5397. It applies
the published almost-simplicity and split-rank transfer theorems to the actual
central isogeny in the definition of `IsSpinCover`. Its field and universe are
arbitrary, and it imposes no characteristic restriction.

For an isometry group that is smooth, an `IsSpinCover q π` supplies a simply
connected source `S` and a central isogeny from `S` onto the connected isometry
group. Simple connectedness, through its semisimplicity field, makes `S`
smooth, connected and affine. If the connected isometry group is almost
simple, the published `IsAlmostSimple.of_isCentralIsogeny` therefore makes
`S` almost simple.

Both source and target of this central isogeny are affine: the source by
semisimplicity and the target as the identity component of the affine
isometry group. The published `IsCentralIsogeny.splitRank_eq` gives equality
of their split ranks. This equality does not require the target almost-simple
hypothesis. In particular, a supplied rank-one equality for the connected
isometry group gives rank one for every spin cover. Together with the
simple-connectedness field, this yields the three properties required by the
host task.

The Prop-valued `SpinCoverPropertiesReductionStatement` packages simple
connectedness and almost simplicity of every spin cover, together with its
split-rank equality with the component, assuming that component is almost
simple. `spinCoverPropertiesReduction` proves it at arbitrary universe `u`.

This unit does not prove smoothness, almost simplicity or rank one for the
quaternionic isometry group, and does not construct a spin cover. These are
separate inputs. The local-field, quaternionic-dimension, nondegeneracy and
Witt-index hypotheses of `LocalSpinRankOneStatement` are not used by these
general transport lemmas. The exact statement of that task remains unproved
by this unit.
