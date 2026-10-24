# Spectral shifts of JPSS integrands and value sets

Worker 85. This is an internal proof helper for the unramified L-polynomial
transport. Its source motivation is JPSS, *Rankin–Selberg Convolutions* (1983),
(2.4), printed page 387, and Theorem (2.7)(ii), pages 390–391 (registered as
`jpss-1983-rankin-selberg`). The transport identities are derived directly
from the Library's integral definitions; they are not quoted source theorems.

The nonzero determinant norm obeys the complex-power addition law. Thus
multiplying the product of the two Whittaker functions by the determinant
weight of exponent `u` shifts each integrand from `s` to `s+u`. For unequal
ranks the exponent offset `(j+k+1)/2` is unchanged. The proof descends the
pointwise identity to the actual left-unipotent quotient.

The definitions `whittakerDeterminantTwist` and
`inverseWhittakerDeterminantTwist` specialize `twistFunctionEquiv` to
multiplication by `χ(det g)` on the two actual Whittaker function spaces.
Triviality of the determinant character on the unipotent subgroup preserves
the defining equivariance, and multiplication by the inverse character gives
the inverse linear map.

The two set-image identities `whittakerSet_twist_image` and
`inverseWhittakerSet_twist_image` repackage the Library's coefficient-model
membership equivalences. They identify the functions of the twisted
representation with the image of the actual character-multiplication linear
equivalence, for both additive-character conventions.

The two value-set lemmas take an equivalence of rational functions and its
rational-continuation shift law as explicit inputs. They do not yet construct
that algebraic equivalence. For images of supplied Whittaker-function sets,
the pointwise integrand shift transports the Bochner integrals and absolute
convergence. A right-half-plane bound `a` becomes `a-u.re` in the forward
direction and `a+u.re` in the reverse direction. Unequal-rank convergence
uses the original product measure while its scalar integral stays iterated,
as in the Library. No normalization, Haar condition, or analytic existence
assumption is imposed on the supplied measures.

The four representation-level lemmas
`equalRankZetaValues_unramified_left`, `equalRankZetaValues_unramified_right`,
`unequalRankZetaValues_unramified_left`, and
`unequalRankZetaValues_unramified_right` instantiate these image identities.
They assume the exact formula `χ(x) = abv(x)^u` on units and the explicit
continuation-shift law. The first member's twist multiplies its Whittaker
function; the second member's twist multiplies its inverse-character
Whittaker function. In unequal rank, the block matrix has determinant equal
to that of its corner, by `determinant_unequalRankMatrix`. Multiplication
associativity and commutativity then supply the integrand shift. The field
and the two representation spaces have independent universes.

This helper alone does not prove `UnramifiedTwistLFactorStatement`; the final
proof must instantiate the explicit rational-continuation input with the
published spectral-rescaling construction and transport normalized Laurent
generators.
