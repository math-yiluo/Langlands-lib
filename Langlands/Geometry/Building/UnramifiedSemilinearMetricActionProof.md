# The complete metric and finite-orbit coefficient action on the unramified building

This module proves the exact published proposition
`Langlands.Geometry.Building.UnramifiedSemilinearMetricActionStatement.{u}`
by the theorem `Langlands.Geometry.Building.unramifiedSemilinearMetricAction`.
It is an internal assembly of the Library's full-V6 integer-valued building
geometry and coefficient-chart constructions. The universe `u` and the
characteristic of the local field are unrestricted.

For every supplied datum `C` on the actual base change to
`inertiaFixedField F`, the order-one unit theorem supplies the hypothesis of
`IntegerValuationBuildingData.exists_retractionDistance`. This constructs an
invariant distance, its prescribed root-distance formula on the original
apartment, and contracting apartment retractions that preserve distance from
each specified apartment centre. The proved common-apartment theorem and
`exists_metric_of_retractionDistance` then give a single metric on the exact
existing `C.ReducedBuilding`, complete and nonpositively curved in the KP
midpoint sense, with its existing rational-point action isometric. The metric
construction discharges normalizer-orbit discreteness internally.

The invariance and original-apartment formula identify the constructed
distance with `C.invariantRootDistance`, hence with the common-apartment
`chosenRootDistance`. The coefficient action is the single homomorphism
`MaximalUnramified.coefficientAction C` supplied by the moving coefficient
charts. Its semilinearity is `coefficientAction_smul`. Each corrected chart
preserves the norm of the original apartment displacement by
`CoefficientChart.norm_vsub`; this norm is defined by the sum of squares of
all relative-root evaluations on the reduced translation space. Applying
`movingAction_isometry` to the identified distance proves that every
coefficient permutation is an isometry for the same metric.

Finally, `coefficientAction_finite_range` proves every orbit finite. Its
finite-type hypothesis follows from the smoothness of the connected
reductive group. Its finite-field stabilizer proof uses generating
cocharacters and finitely many rational-point witnesses for each point; it
does not require a torus or apartment defined over the base field.

All witnesses live on the original quotient, and the rational-point action
and coefficient conjugation are the existing Library objects. The proof
adds no stable apartment, special torus, metric, point or model as a
hypothesis and does not assert existence of the supplied datum. It leaves
the target statement and its imports unchanged. Only the generic safe
metric and retraction modules are imported, so no downstream special-torus
or simultaneous fixed-point statement is used.

The construction follows the internal interfaces associated with
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Section 4.2
(metric, curvature and completeness), Sections 7.6 and 7.9 (the quotient
and transport), and Section 9.2.1 (coefficient semilinearity), with the
corrections of 1 November 2024, pages 27–29, 33 and 39. Those original-source
comparisons belong to the paired prerequisite developments and the
published statement; this assembly introduces no additional literature
assertion. In particular, the implemented root-coordinate norm gives the
required simultaneous isometries directly, and the finite-field witness
argument supplies finite orbits without a globally stable apartment.
