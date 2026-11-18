# All-test module charts from actual coproduct components

This internal prerequisite for the relative radical filtration constructs the
actual component point and relative-section identifications on every test
scheme over a coproduct base. It uses actual pullback tests, their original
inclusions, and canonical module-pullback composition comparisons. Neither
the index set nor the test scheme must be finite or nonempty.

`pointsEquiv` assembles actual group points from arbitrary component pullbacks,
using the fully faithful restriction to a scheme coproduct's components.
Multiplicativity follows from the actual multiplicative base-change point
adjunction and composition with the original component inclusion.
`sectionsEquiv` applies actual disjoint-cover section gluing on each test.
Its component value is the canonical relative section pullback along that same
inclusion.

`ComponentCharts` records natural all-test point/section charts of the actual
restricted group in the actual restricted module. `pointSectionEquiv` assembles
them, retaining the canonical composition comparisons. Its component recovery
equation is proved, and naturality follows by applying the component section
equivalence, the original component charts' naturality, the canonical module
composition comparison, and naturality of the pullback adjunction counit.

For a supplied module already proved finite locally free, and a group already
proved smooth and affine over the coproduct base,
`ComponentCharts.isVectorBundleAdditive` derives the unchanged all-test
vector-bundle additive predicate. The component charts are explicit inputs to
this general assembly theorem. The later face-cover specialization must
construct them from its actual free vector groups and actual free-module
component comparisons. Descent from the coproduct chart base to the original
base, including its linear transition cocycle, is a separate obligation.

Provenance: an internal derivation from actual disjoint-component morphism
assembly, disjoint module-section gluing, the multiplicative base-change point
adjunction, and the canonical relative-section pullback identities.
