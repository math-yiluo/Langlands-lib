# Positive root cones and strict split-component bounds

Author: Worker 1682.

This internal supporting module derives norm bounds from the published
represented-parabolic positive root cone. It does not prove Casselman's
criterion.

A real linear functional nonnegative on every generator of a finite cone
is nonnegative on its nonnegative combinations. If it is positive on one
generator, it is positive on every combination having all coefficients
positive. The Lean proofs expand the finite sum and use the signs of its
individual terms.

Apply the second fact to pairing with the actual valuation of a
split-component point. The published all-point norm formula expresses the
character norm as `q` to the negative of this pairing. Since `q > 1`,
a positive pairing implies norm strictly below one.

The split-component point homomorphism has central image in the literal
Levi point image. Recording that centrality gives
`splitComponentCenterPointsMap`. A full-center exponent restricts along
this map to a normalized Jacquet exponent: continuity preserves the open
kernel, and the published inclusion of uniform generalized central spaces
in the split-component weight space preserves nontriviality. This uses no
Jacquet admissibility, weight decomposition, irreducibility or finite length.

The last theorem combines these facts. A positive-cone condition for every
split-component exponent bounds any full-center exponent at every point
coming from the split component with nonnegative restricted-root
valuations and at least one positive valuation.

This is an internal deduction from the Library constructions and norm
formula, using the `q^(-s)` convention. Renard V.3.14–V.3.15 and V.3.20–V.3.21
explain its role in the criterion, but no new source equivalence is asserted.
The module does not construct compatible presentations or lift arbitrary
central torus test points to the split component. Matching the standard and
represented Jacquet modules, the geometric existence statements and the
analytic implications of the full criterion remain separate obligations.
