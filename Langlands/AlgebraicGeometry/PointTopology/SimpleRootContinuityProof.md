# Continuity of a simple root via the product-domain implicit function theorem

Author: Worker 208.

`Langlands.AlgebraicGeometry.PointTopology.monicSimpleRootContinuity` proves
`Langlands.AlgebraicGeometry.PointTopology.MonicSimpleRootContinuityStatement`
in arbitrary common universe `u`. It keeps the actual finite-sum monic
polynomial family from the statement.

The implementation builds a strict Fréchet derivative of joint polynomial
evaluation from coefficient projections, powers, multiplication and finite
sums. Restricting this derivative to the root variable and using uniqueness
of derivatives identifies it with multiplication by the evaluated formal
derivative. A nonzero simple-root derivative has an explicit continuous
linear inverse.

Mathlib's product-domain implicit function theorem then supplies the root
branch, its continuity, its base value, the eventual root identity and
uniqueness in a product neighborhood. Continuity of joint evaluation of the
formal derivative ensures that the nearby chosen roots remain simple.
The product-domain theorem works over arbitrary complete nontrivially
normed fields, so the argument does not impose characteristic zero.

The original-source motivation and correction to unrestricted epsilon-ball
uniqueness are recorded in the unchanged statement Markdown. This proof
does not implement the later scheme-theoretic reduction to polynomial
presentations or prove smooth point-map openness.
