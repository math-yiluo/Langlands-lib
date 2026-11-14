# Laurent functions bounded on uniformizer-power tuples

This derived helper uses character extraction to show that a Laurent function
bounded on every integer-power tuple of a unit of nonzero integer valuation is
constant. Integer-power tuples form a group. Their distinct monomial characters
are separated by valuation. Each nonconstant character has unbounded values,
as its logarithmic valuation contains a nonzero integer multiple of a free
integer parameter. The character-component extraction lemma therefore forces
all nonconstant coefficients of a bounded Laurent function to vanish.

`powerTuple` sends a tuple of integer exponents to the corresponding powers
of the chosen unit. `powerMonomial` restricts a Laurent monomial to these
tuples. `powerMonomial_injective` proves separation by evaluating on tuples
supported at a single coordinate and taking logarithmic valuations.
`coefficient_eq_zero_of_bounded` uses the Archimedean property of the integers
to exclude a nonzero bounded multiple of a nonconstant character.
`eq_constant_of_bounded` expands the Laurent function as a finite character
sum, applies bounded character-component extraction, and checks every
coefficient. The hypothesis is nonzero logarithmic valuation; no residue
field hypothesis is required.
