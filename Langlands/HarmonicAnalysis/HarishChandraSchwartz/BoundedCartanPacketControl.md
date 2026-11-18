# Full-height seminorm controls on bounded-root Cartan cells

This module is internal analytic glue for the bounded-root part of the
wave-packet argument. It combines the actual height comparison in
`RationalCartanCentralHeight` with elementary real-power inequalities and
scaling of the existing input seminorms. No new original-literature theorem
or new topology is asserted. All declarations are in
`Langlands.HarishChandraSchwartz`.

For any complex module `E`, a family `P r` of input seminorms and real numbers
`D` and `r`, `heightComparisonSeminorm P D r` is
`Real.toNNReal (D^(max r 0))` times `P (max r 0)`.
`heightComparisonSeminorm_apply` gives its real-valued formula for `D >= 0`.
Thus each output control uses just one of the existing input controls and a
nonnegative scalar multiplier.

The pointwise theorem `norm_le_heightComparisonSeminorm` concerns any family
`f : E -> X -> complex`, weights `Xi`, `sigma` and `tau`, and a point `g`.
Assume `D >= 1`, nonnegativity of the three weights at that point, and
`1 + sigma(g) <= D * (1 + tau(g))`. A central decay bound for `f(q)(g)` at
order `s = max(r,0)`, with input factor `P s q`, then implies the full-height
bound at order `r` with input factor `heightComparisonSeminorm P D r q`.
The proof raises the height comparison to the nonnegative power `s`, takes
reciprocals of positive quantities, and obtains
`(1+tau)^(-s) <= D^s * (1+sigma)^(-s)`. Since `s >= r` and `sigma >= 0`,
this is at most `D^s * (1+sigma)^(-r)`. Nonnegativity of the seminorm and Xi
justifies multiplication. This also covers negative real output orders and
the endpoint `r = 0`.

`continuous_heightComparisonSeminorm` proves continuity in any given topology
on `E` if every `P r` is continuous there. It is just continuity of a fixed
nonnegative scalar multiple; no comparison of input topologies is made.

On actual rational points, `exists_fullHeightControl_on_bounded_cartan_cells`
takes a connected reductive group over an arbitrary nonarchimedean local
field, maximal split torus, generic cocharacter, compact subgroup `K0`, finite
set `F0` of centralizer points, arbitrary finite matrix representation `rho`,
and a fixed nonnegative root bound `T`. Suppose that every `f(q)` has central
valuation decay of every real order, controlled by `P r q` times the same
nonnegative Xi weight. The result chooses one `D >= 1`, before the varying
order, input, cocharacter and group point, such that

`norm (f q g) <= heightComparisonSeminorm P D r q * Xi(g)
                   * (1 + rationalHeight rho g)^(-r)`

for every Cartan cell whose cocharacter has all absolute simple-root pairings
at most `T`, and every point in that cell. The height comparison is proved
from these actual data by the preceding module, rather than assumed as an
additional analytic hypothesis. There is no norm-kernel restriction and no
closed-immersion requirement on `rho`.

For wave-packet application, `P` can be the continuous source-normalized central
control of `StandardLeviPlancherelWavePacketCentralControl`, with its original
packet as `f` and actual rational Xi as the weight. The present theorem is a
generic bound and does not itself discharge that module's retained structural
inputs. The bounded-root cells are only one part of the full group argument;
this module proves no Cartan-cover existence, unbounded-region estimate,
global Schwartz membership or Schwartz-valued synthesis continuity.
