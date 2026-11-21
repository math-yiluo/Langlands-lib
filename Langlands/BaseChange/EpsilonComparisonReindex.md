# Reindexing an epsilon monomial comparison

`EpsilonComparisonReindexStatement` transfers an epsilon monomial product
comparison from a finite index type to a finite set via a supplied equivalence.
The lower exponents agree at corresponding indices, and the single upper
exponent agrees. Each comparison uses the same lower and upper residue bases.
The nonzero coefficients may vary.

Write the lower monomial products as a product of coefficients times a product
of spectral powers. Reindex the powers using the given equivalence. Multiply
the original comparison constant by the ratio of the two lower coefficient
products and the inverse ratio of the upper coefficients.

This is an algebraic step from the global Hecke index to the local norm
character index after the distinguished-place comparison in Arthur–Clozel,
Chapter 1, proof of Proposition 6.9(ii), equation (6.17).
