# Finite Rosati equations for the Harris order

This internal comparison uses the actual positive auxiliary left involution,
the full integer order and its finite basis, and the existing constructed dual
of a supplied abelian scheme. The arithmetic types are universe zero, as in the
normalized Harris moduli problem; the scheme universe is independent.

`IntegralRosatiBasisEquations` requires, for each basis element `b_k`,
the actual equality
`a(b_k) ≫ λ = λ ≫ dual(a(τ(b_k)))`.
Here `a` is a supplied unital integral order action and `τ` is exactly the
restriction of the positive auxiliary left involution. The dual witnesses,
evaluation, geometry and named tensor and Picard premises are explicit.
No polarization predicate or existence of such data is asserted by these
equations.

`RationalRosatiBasisEquations` expresses the corresponding finite equations
in the actual rational Hom group, for an arbitrary rational homomorphism `λ`.
`rationalAction_involutionCompatible_iff` identifies those equations with the
published `IsInvolutionCompatible` predicate for the unique rational extension
of `a`. Its star instance is the existing `auxiliaryStarRing D C`.
Both sides of the Rosati equation define rational linear maps on the ambient
algebra: composition is bilinear, dualization is rational linear, and the
positive auxiliary involution fixes the rationals. Equality of these maps
reduces to the rational basis obtained from the full integer order. The
extension agrees with the supplied rationalized integral action on the whole
order, and the involution preserves that order, giving exactly the stated
finite equations.

`IntegralRosatiBasisEquations.rationalize` applies the canonical map to the
actual integral equality and uses the published compatibility of composition
and dualization with rationalization.
`rationalAction_involutionCompatible_of_integralBasis` combines that result
with the basis criterion. It applies in particular when `λ` is an actual
polarization. No injectivity of integral Hom into rational Hom is used or
claimed, and no converse from rational equations to actual equalities is
asserted.

The provenance is internal linear algebra and functoriality of the existing
dual and rationalization constructions. This unit supplies only Rosati
compatibility for a supplied integral action and supplied dual data. It
constructs no integral action from rational data, no polarization, no moduli
scheme, and no normalized representability comparison.
