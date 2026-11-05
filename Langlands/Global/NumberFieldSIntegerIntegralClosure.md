# Actual number-field S-integer integral closure

This derived construction supplies the number-field integral-closure comparison
needed by Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
Example 4.2, printed pages 9–10. For an embedding of the original number fields,
the integers outside the full upper preimage of a finite set of lower finite
places are exactly the integral closure of the lower S-integer ring in the
original upper field. The resulting ring equivalence fixes every underlying
upper-field element.

The local argument first proves that an element integral at every original upper
finite place over a lower place is integral over that lower valuation ring.
Let V be the lower valuation ring and C its integral closure in the upper field.
The finite separable number-field extension makes C a Dedekind domain with the
upper field as fraction field. The original upper ring of integers maps into C
because its elements are integral over the lower ring of integers and hence over
V. Every height-one prime Q of C contracts to the maximal ideal of V and then
to the specified lower prime. Its contraction to the upper ring of integers is
therefore nonzero and defines an original upper finite place q over that prime.
The localization at q is contained in the valuation ring of Q: a denominator
outside q has valuation one at Q. The discrete valuation overring comparison
identifies these two valuation rings. The hypothesis thus places the element in
every height-one localization of C, whose intersection is C.

For an upper S-integer this local criterion applies at each lower place outside
the exceptional set. The integrally closed local valuation ring has the original
lower field as fraction field, so its minimal polynomial maps to the field
minimal polynomial. Every coefficient of the latter is consequently a lower
S-integer. Coefficientwise polynomial lifting gives a monic polynomial over the
actual lower S-integer ring; compatibility of the original field embedding with
evaluation makes the given upper element its root. This proves the reverse
integral-closure inclusion. The forward inclusion is the valuation-ring argument
already implemented in `ArithmeticSIntegerExtension`.

Both number fields inhabit an arbitrary common universe, and the algebra map
is the original field embedding. The finite exceptional set may be empty; only
finite places occur in these S-integer rings. Finite local freeness and the
integral and adelic Weil comparisons remain obligations of the host task.
