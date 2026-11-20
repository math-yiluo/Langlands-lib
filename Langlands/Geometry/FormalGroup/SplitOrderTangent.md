# The tangent of the division-order summand

An action of \(B^{\mathrm{op}}\times B\) on a coordinate formal
module gives the two order projectors. `divisionTangent` is the
image of the derivative of \((0,1)\) over a specified coefficient
test ring. It is also the module of fixed vectors of that
projector. The derivative of \((0,b)\) restricts to this image,
and `divisionTangentAction` makes it a unital representation of
the actual order \(B\).

The derivative of an order-linear formal map intertwines the
projectors and their restricted actions. Consequently an actual
order isomorphism induces a linear equivalence of the summands
which intertwines the \(B\)-actions. Taking the summand after
coefficient pullback uses the composite coefficient map and the
same tangent vectors.

Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996),
§6.43, printed pp. 308–309 (PDF pp. 320–321), use the split
order to pick out the factor on which the special condition is
imposed. The Lean construction provides its tangent summand in
the order \(B^{\mathrm{op}}\times B\), with \(B\) in the second
coordinate. The special character condition is an additional
property of this summand.
