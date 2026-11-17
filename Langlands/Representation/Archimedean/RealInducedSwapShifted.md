# Four crossings with a common recurrence shift

This internal unit generalizes the recurrent four-crossing construction to a
common additive shift in the four recurrence parameters, while keeping the
source and target exponents fixed. Its provenance is the published rank-three
landing theorem with arbitrary recurrence parameter, induction in stages,
Fourier uniqueness, and the existing two-window membership criteria.

`Crossing x y ζ` consists of a multiplier with reflection symmetry for the
crossing `x,y` and recurrence parameter `x.exponent-y.exponent+1+ζ`.
`FourCrossings d e ζ` supplies these sequences at BC, AC, BD, and AD. Reflection
symmetry gives each actual Frobenius map between the fixed standard modules.

The induced-first rank-three landing uses parameters δ and δ+|weight|, and the
character-first landing has the same relation. A common shift preserves that
relation. Consequently two successive induced-first landings move the first
source induction window to its target position. Two character-first landings
move the second window. The middle crossings lie on disjoint coordinate pairs,
so their commuting square identifies both paths with the same four-factor map.
The existing induction-in-stages theorem transports each local landing to rank
four. Compact vanishing and the actual target membership criterion then
corestrict the map to `shiftedMap` between the two induction-block spaces.
Every factor commutes with right compact translation, so the corestricted map
does also. At zero shift, `FourCrossings.toRecurrent` supplies the ordinary
recurrent crossing data; equality of the underlying maps transfers the existing
exact compact and Lie intertwining theorem to `shiftedMap_zero_modulo`.

The code follows the recurrent construction, reusing its list models, compact
inclusions, window membership lemmas, and the published landing and disjoint
commutation theorems. The new mathematical point is that the shared shift need
not equal zero; no relation between this shifted recurrence and the fixed Lie
actions is asserted. This unit proves no injectivity, parameter regularity, or
full swap equivalence.
