# Proof of the elementary Harish-Chandra boundary targets

Author: Worker 200. This proves the published
`Langlands.CuspidalSupport.HarishChandraBoundaryStatement`.

`isSmoothVector_restrict_open_iff` proves the general open-subgroup comparison
without assuming smoothness of the representation or continuity of its action.
For a vector fixed by an open subgroup of the open subgroup, it maps that
fixing subgroup into the ambient group. Its image is open because the subgroup
inclusion is an open map. Conversely it pulls an ambient open fixing subgroup
back along the continuous inclusion, using the published smooth-pullback lemma.

`determinantUnitSmoothDual` applies this comparison to the original dual
representation and the actual determinant-unit open subgroup. The dual of the
restricted representation is definitionally the restriction of the dual, so
this proves precisely the restricted-dual condition in the statement.

For `leviHarishChandraRankZero`, each positive block size is at most the sum
of all block sizes, which is zero. Thus the block index type is empty. Its
product Levi is a singleton, so every refined parabolic equals the whole group
and the premise for any quasicuspidality test is false. The determinant-unit
subgroup is also a singleton. Every function on this compact domain has compact
support, including every required coefficient. No condition on the dimension
or nontriviality of the carrier enters the argument.

`harishChandraBoundary` pairs the two results and has the exact proposition
`HarishChandraBoundaryStatement.{uF,uV}` as its type. Field and carrier universes
are independent. The original full Harish-Chandra target and its imported pairs
are unchanged. This proof does not establish the positive-rank equivalence.
