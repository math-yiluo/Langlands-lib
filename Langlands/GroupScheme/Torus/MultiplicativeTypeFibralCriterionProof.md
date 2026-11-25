# The fibral criterion for groups of multiplicative type

`Langlands.GroupScheme.multiplicativeTypeFibralCriterion.{u}` proves
`MultiplicativeTypeFibralCriterionStatement.{u}`. It establishes the
connected-fibre criterion and the commutative torsion-order criterion for
flat, affine, locally finitely presented group schemes over arbitrary bases.
The statement formalizes Brian Conrad, *Reductive group schemes* (2014),
Theorem B.4.1, pp. 297–299.

For necessity, the proof passes relative multiplicative type to each geometric
fibre. In the commutative branch, it also uses local constancy of the coordinate
dimensions of the positive torsion schemes.

For sufficiency, work on the affine open cover of the base. At each point of an
affine chart, `strictLocalEtaleLimitExistence` supplies a strictly Henselian
local limit of affine étale neighbourhoods. Pull back the original group
along the map from the limit to the chart followed by the chart inclusion.
The group retains flatness, local finite presentation and affineness.
Connectedness of the residue fibres and multiplicative type of the geometric
fibres pass to this base change. In the commutative case, commutativity also
passes to the pullback, and the geometric torsion order function upstairs is
the composite of the original function with the continuous base map.

The strict-Henselian criteria apply `multiplicativeTypeStrictHenselianLift`
to a splitting of the special fibre. The lifted open and closed immersion is
an isomorphism by fibre connectedness in the first branch and by torsion-order
comparison and torsion determination in the second. The base-change
composition isomorphism identifies the resulting group on the limit with the
pullback of the group on the affine chart.
`LocalMultiplicativeType.of_pointwise_localBaseChange` spreads these local
presentations to fppf diagonalizing neighbourhoods. Open-cover descent
then gives multiplicative type on the original base.
