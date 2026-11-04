# Conditional tangent containment in a Cartan subgroup

This module assembles the nilpotent quotient portion of Milne,
*Algebraic Groups* (2017), Proposition 17.90, printed p.381 / PDF p.397,
for actual group schemes over every field `k : Type u`.

`Lie.cartanTangentFactor` starts with a maximal torus `i : T → H` in a
smooth affine group and a closed representative `d : D → H` of its
whole-torus centralizer. A tangent vector `X` is fixed by `T` on every
test scheme. The construction assumes that `D` is connected and
geometrically nilpotent, and that every tangent lift of `X` through `d`
is semisimple in the published representation-tested sense. The last
assumption is a local reflection premise, not a consequence asserted here.
The exact propositions `NilpotentCentralTorusStatement` and
`UnipotentSemisimpleStatement` also remain explicit inputs.

The existing all-test torus-centralizer symmetry gives an actual tangent
lift into `D`. Published smoothness of torus centralizers gives smoothness
of `D`; its closed inclusion in affine `H` gives affineness. The original
torus factors through `D`, and maximality in `H` makes this factor maximal
in `D`. The nilpotent tangent adapter then lifts the vector further into
that prescribed torus. The reconstruction theorem composes the two
tangent identities and the torus factorization identity.

`Lie.range_le_elementCentralizer_of_mono` is an elementary auxiliary
reflection result. It reflects all-test commutation along a monomorphic
homomorphism by cancellation on dual-number points. It does not assert
reflection of semisimplicity.

The structural premises correspond to the smooth connected nilpotent
Cartan conclusion of Milne Proposition 17.44, printed pp.364–365 / PDF
pp.380–381. Only smoothness is discharged in this module. The registered
2017 errata snapshot dated 2026-11-02 contains no correction to 17.44 or
17.90. This is a derived construction and conditional reduction toward
Cartan generation; it does not prove those structural premises or the
exact Cartan generation statement.
