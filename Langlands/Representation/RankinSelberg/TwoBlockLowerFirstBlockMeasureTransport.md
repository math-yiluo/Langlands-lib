# The prescribed lower-unipotent measures

This internal support module for JPSS (1983), Sections 4.7 and 4.9,
uses the actual lower-unipotent subgroup and block rotation already defined
in `TwoBlockLowerUnipotentQuotientData`. It retains every canonical p-adic
field and positive two-block shape. It proves measure transport and
compatibility; it does not assert a lower mixed disintegration.

The measure `lowerHaar` is exactly the pushforward of the fixed standard
unipotent Haar by the inverse of conjugation by the block rotation. The
continuous multiplicative equivalence transfers the Haar property and
regularity. Right translation commutes with this equivalence after translating
by the corresponding standard element, so the pushforward is right invariant.

The quotient homeomorphism uses left multiplication by the block rotation.
Its inverse therefore sends the class of `g` to the class of `C⁻¹ g`.
For every complex function, the lower orbital average at this transported
class is the standard orbital average of `x ↦ f(C⁻¹ x)`. The proof changes
variables in the total Bochner integral using the inverse-conjugation
homeomorphism, then cancels the adjacent rotation factors. This identity
needs no integrability premise.

For every compatible standard quotient measure, its prescribed inverse
quotient pushforward is compatible with the fixed ambient Haar and
`lowerHaar`. Nonzeroness and regularity pass through the quotient
homeomorphism. The homeomorphism commutes with right translation, giving
right invariance. For each compactly supported continuous complex test
function, the exact average identity transfers integrability and the Weil
formula from the standard quotient. Ambient left invariance removes the
remaining translation by `C⁻¹`. Finally, regularity on the locally compact,
second countable standard quotient gives sigma-finiteness, which passes
through the measurable quotient equivalence to the lower measure.

The original JPSS lower subgroup and quotient conventions motivate the
construction (printed pages 413 and 416–418). The compatibility and
sigma-finiteness arguments here are derived measure-theoretic support.
