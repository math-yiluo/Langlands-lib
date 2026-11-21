# Products of actual p-divisible groups

`PDivisibleGroup.prod` takes the actual binary product of the two group schemes
at every level. The inclusions and transfers act componentwise. The structure
map factors through a pullback projection, so each product level is finite
locally free. Its scalar relation follows from the two projection equations for
multiplication.

`AffineFppfShortExact.prod` verifies componentwise injectivity and identifies the
kernel with the image of the product inclusion. For local surjectivity it first
lifts one point after an affine fppf extension. It lifts the other point over a
second affine fppf extension and transports the first lift there. The composite
extension is affine fppf, and the two lifts give a point of the product over that
extension.

This is the componentwise construction for the finite levels and exact
sequences in Tate, *p-Divisible Groups* (1967), §2.1, equation (2), printed
p. 161 (PDF p. 2). Every level is the product of the original schemes over
the original base.
