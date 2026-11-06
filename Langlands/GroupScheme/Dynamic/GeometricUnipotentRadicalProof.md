# The full geometric radical theorem for dynamic parabolics

Author: Worker 1281.

`Langlands.GroupScheme.dynamicGeometricUnipotentRadical` proves exactly
`Langlands.GroupScheme.DynamicGeometricUnipotentRadicalStatement.{u}` for
arbitrary universe `u`. For every field `k`, connected reductive group
scheme `G` over `Spec k`, and cocharacter `χ`, take arbitrary compatible
representatives `p : P → G` and `r : U → P`: `p` represents the actual
dynamic parabolic and `r ≫ p` represents the actual identity-limit subgroup.
The theorem concludes the existing `IsGeometricUnipotentRadical r`.

The implemented proof applies the published
`dynamicGeometricUnipotentRadical_of_centralizer` to the published theorem
`dynamicCentralizerReductive`. The reduction has precisely
`DynamicCentralizerReductiveStatement.{u}` as its premise; the centralizer
theorem proves that proposition without further assumptions. This application
discharges the reduction's remaining premise.

The reduction derives closedness of `r`, smoothness and connectedness of
`U`, unipotence from the torus-action unipotence theorem, and normality in
`P`. It also establishes connectedness, unipotence and normality after
base change to `AlgebraicClosure k`. Connected reductivity of the represented
dynamic centralizer supplies the geometric radical-vanishing input to
`Dynamic.GeometricMaximality`. Its factorization theorem puts every smooth
connected normal unipotent closed subgroup of the base-changed `P` in the
range of the base-changed `r`, including subgroups that do not descend to
`k`. Thus the conclusion includes the full geometric greatestness clause.

All representation, normality and containment predicates retain their
existing meanings on every test scheme, including nonreduced tests.
The field, cocharacter and compatible representatives remain arbitrary;
there is no splitness, perfectness or characteristic restriction.
Unipotence and radical identification are conclusions.

This pair is an internal composition of published Library results. The
target and its imported definitions are unchanged. The imported reduction
and centralizer proof pairs explain their implemented arguments and
provenance; this final application adds no external structural assertion
or citation. Representability, smoothness, connectedness and centralizer
reductivity are reused from their published modules, which retain their
own authorship. General dynamic parabolicity remains independently owned
and is not required by this composition.
