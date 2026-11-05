# Finite locally free actual curve S-integers on cofinal principal levels

This derived construction supplies the function-field arithmetic input to the
integral Weil restriction in Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), Example 4.2, printed pages 9–10. Use the actual exceptional sets
constructed in `CurvePlacePrincipalSInteger`: the poles of a parameter s together
with the poles of the inverse of a nonzero element t of the normalized parameter
chart. These exceptional sets contain any prescribed finite set of original
curve places, as already proved there. The upper exceptional set is the full
inverse image under the original place restriction.

The scoped instances in `CurvePlacePrincipalSIntegers` first construct the
original normalized-chart map into the actual lower S-integer ring. Outside the
exceptional set the parameter is integral, so each normalized-chart element is
integral in the relevant valuation ring. The ring equivalence already proved in
`CurvePlacePrincipalSInteger` respects this chart map. It therefore transfers the
actual away-localization structure to the S-integer ring, with the original
field as fraction field. The lower ring is Dedekind by localization. The away
localization is finitely presented over the finite normalized chart, so the
lower ring is also of finite type over the original finite constant field.

The actual upper S-integer ring is identified as the lower ring's integral
closure in the original upper field by the previously proved
`curvePlaceSIntegers_integralClosure_eq`. Finite constants make the lower ring
of finite type over the integers. Its derived normality, Noetherianity and
original fraction field instantiate
`finite_integralClosure_of_normal_integer_finiteType`, which gives finite
normalization in every finite extension, including inseparable ones. The
integral-closure algebra equivalence transfers this module finiteness to the
actual upper S-integer ring. Its embedding into the original upper field gives
torsion-freeness. Over the lower Dedekind domain it is flat; finiteness gives
finite presentation, so it is projective. The explicit local-freeness theorem
proves freeness of the upper module at every prime of the actual lower ring.
The generic module rank is the original field degree.

`curvePlacePrincipalSIntegersFractionTensorEquiv` constructs the original
generic-fiber algebra: tensoring the actual upper integer ring with the original
lower field over the actual lower integer ring gives the original upper field.
The construction reuses localization of the actual integral closure. The
pure-tensor formula preserves the original field embedding and the original
upper integer inclusion.

All fields inhabit an arbitrary common universe. Finite constants, a lower
function-field presentation, finite degree over the specified parameter
subfield, compatible constant-field algebras and the finite original field
extension are explicit. The `Fact` premise is exactly nonzeroness of t; it is not
an assumed normalization, finiteness or projectivity package. No separability
assumption occurs. This result covers the proved cofinal family of principal
exceptional sets; it does not assert finite local freeness for every arbitrary
finite exceptional set. The actual integral Weil generic fiber and adelic
topological comparison remain obligations of the host task.
