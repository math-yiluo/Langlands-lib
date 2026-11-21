# Integral normalization at every regular parameter

`compactTestSectionValues` uses the actual unramified character transport to
extend one fixed compact-picture section and restrict it to a test space.
Its values at each test point are polynomial via evaluation of a single
unramified character. Local constancy is uniform in the parameter, and compact
support at one parameter gives common compact support.

`exists_compactTestPolynomialIntegral` integrates this family at a measure
finite on compacts. It gives a polynomial vector family on the entire
parameter space whose linear tests are the scalar integrals, together with
compact support of the test restriction at each twist. This finite
integration construction also applies when a continued operator has a
vanishing denominator.

`continuedOperator_compactTest_integral` assumes a weak integral identity on a
nonempty open part of the original domain. The finite fiber integral recovers
the weak representing vector there by uniqueness. Its polynomial dependence
and the continuation identity extend the equality throughout the selected
regular region. The finite fiber integral then gives the identity against all
algebraic linear forms, together with their scalar integrability. The proof
uses the Library's compact-picture extension and finite integral.
