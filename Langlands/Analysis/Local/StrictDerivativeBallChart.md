# Centered Haar charts from a strict derivative

Compose the map with the inverse of its strict derivative. On sufficiently
small closed balls around the origin, the normalized map is the identity
plus a perturbation of Lipschitz constant at most one half. Extend the
perturbation by zero across the complement of the clopen ball for the
application of `map_closedBall_add_perturbation`.

For each point of the ball, subtraction of the perturbation from the
desired point defines a contraction of the ball. Its fixed point proves
surjectivity. The strict Lipschitz inequality also proves injectivity.
The continuous bijection from the compact ball to its open image is an
open embedding. Applying the derivative to the normalized Haar
pushforward gives the stated restriction of additive Haar transported
by the derivative.
