# Actual curve S-integer Weil generic fiber on cofinal principal levels

This derived construction supplies the function-field generic-fiber comparison
for the integral Weil model in Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), Example 4.2, printed pages 9–10. It uses the actual curve
S-integer ring at a principal exceptional set from
`CurvePlacePrincipalSInteger`, and the actual upper S-integer ring at its full
upper inverse image. These principal exceptional sets were proved to contain
any prescribed finite set of original curve places.

For a scheme Y over that actual upper ring, locally of finite type and equipped
with a specified relative immersion into finite-dimensional projective space,
`curvePlacePrincipalSIntegersWeilGenericFiberIso` constructs an isomorphism over
the spectrum of the original lower field. Its source is the original-field base
change of the actual integral Weil-restriction scheme. Its target is the actual
field Weil-restriction scheme of the original upper-field base change of Y.
The relation between the projective immersion and Y's structure map is explicit.

The construction specializes
`projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso` to these
actual arithmetic rings. `CurvePlacePrincipalSIntegerFinite` proves the lower
ring's original fraction field and identifies the upper ring with its actual
integral closure, finite and projective over the lower ring. Those arithmetic
facts are derived from the normalized-chart localization and finite
normalization; they are not fields of assumed model data. The projective
immersion supplies separatedness and affine neighborhoods of finite subsets,
which give the required Weil-restriction geometry. The original integral-closure
fraction tensor preserves the original coefficient maps.

`curvePlacePrincipalSIntegersWeilGenericFiberIso_comparison` proves equality of
the original counit comparisons on every test scheme over the original lower
field and every morphism from that test into the source. The field Weil counit
after the constructed isomorphism equals the specified integral counit comparison
through the original fraction tensor. Thus the scheme isomorphism retains the
intended original point maps.

All fields inhabit an arbitrary common universe. Finite constants, the original
lower function-field presentation, a parameter subfield of finite degree, the
nonzero chart denominator and compatible finite original field extension are
explicit. No separability premise occurs. The denominator `Fact` expresses only
nonzeroness. This construction applies to the proved cofinal principal family,
not to an assumed finite-local-freeness package for arbitrary exceptional sets.
The hypotheses state local finite type and the specified relative projective
immersion. The adelic topological comparison remains an obligation of the host
task.
