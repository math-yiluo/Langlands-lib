# Pointed étale lifting from smooth subgroup charts

`multiplicativeTypeEtaleLift_of_chartCover.{u}` proves the unchanged
`MultiplicativeTypeEtaleLiftStatement.{u}` under the explicit
`MultiplicativeTypeSubgroupModuli.ChartCoverStatement.{u}` hypothesis.
It requires no global subgroup-moduli scheme or gluing theorem.

Apply the field-point coverage condition to the original subgroup
in the specified residue fibre. It gives a chart and an actual point
over that same residue field, whose evaluated range is the original
subgroup functor. The chart is smooth over the base, so the published
pointed étale section theorem extends this point to a section over a
residually trivial étale neighbourhood. Pull back the chart's closed
multiplicative-type family along the section. Closedness and
multiplicative type persist under base change.

Composition of family evaluation shows that the fibre range is
exactly the prescribed range. The previously constructed
`recover_subgroup_fibre_inclusion` identifies the source groups and
supplies precisely the raw pullback and equality-transport equation
of the original target.

This is an internal derived assembly from the chart interfaces,
pointed étale sections and represented-subgroup uniqueness. The
chart-cover premise remains unproved here. It is a conditional
consequence toward Conrad's Proposition 3.1.6, not an unconditional
proof of that proposition.
