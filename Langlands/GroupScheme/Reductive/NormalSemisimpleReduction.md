# Normal semisimple subgroups under full-centre containment

This internal construction belongs to Worker 1566's proof of generation by
normal almost-simple subgroups. It proves a conditional reduction over every
field, with arbitrary characteristic and universe, from the published
`NormalReductiveCenterStatement` to semisimplicity of smooth connected
closed normal subgroups of a semisimple group.

`finiteCenterOfNormalSemisimple` constructs actual `FiniteCenter H` data.
The existing normal-subgroup theorem first makes `H` connected reductive.
The ambient finite centre supplies a representative `ZG`, and the existing
centre-existence theorem supplies a representative `ZH` of the full centre
of `H`. Under the explicit full-centre containment premise, the published
`normalCenterMap` embeds `ZH` as a closed subgroup of `ZG`. Its closed
immersion is finite, so its composite with the finite structure map of `ZG`
is finite. The construction returns `ZH`, its original inclusion into `H`,
the full all-test centre equality, and this finite structure map.

The companion theorem
`IsSemisimple.of_normalSubgroup_of_normalReductiveCenterStatement`
combines the unconditional reductivity theorem with those finite-centre
data. Neither centre is required to be smooth or reduced, and no test
scheme is discarded.

The provenance is the internal composition of the published
`Reductive.NormalSubgroup`, `Reductive.NormalCenterDescent`, and
`Reductive.FiniteCenterBaseChange` interfaces. The code implements the
construction just described. Full-centre containment remains an explicit
unproved structural premise in this file. This reduction supplies neither
an unconditional normal-subgroup semisimplicity theorem nor the assigned
almost-simple generation theorem.
