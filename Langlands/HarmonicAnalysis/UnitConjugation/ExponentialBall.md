# The exponential in small ultrametric balls

For a complete ultrametric normed algebra over a nontrivially normed ultrametric field of characteristic zero, `ExponentialBallTransportStatement` gives a radius bound such that `x ↦ exp x − 1` is an isometric bijection of every positive-radius closed ball at zero below that bound. With the Borel σ-algebra and properness of the algebra, this map preserves every additive Haar measure restricted to the ball.

The strict derivative of `exp − 1` at zero is the identity. On a small neighborhood the difference from the identity is Lipschitz with constant at most `1/2`. The ultrametric inequality then identifies the distance between two images with the distance between their inputs. Restricting the local inverse chart to that neighborhood and taking a ball inside its source and target gives a bijection of the ball. For the measure identity, the proof extends the perturbation by zero outside the clopen ball and applies `map_closedBall_add_perturbation`.

Clozel, *Characters of non-connected, reductive p-adic groups*, Canadian Journal of Mathematics 39 (1987), §3.5 and the proof of Lemma 9, printed pp. 156–158, uses exponential coordinates and the resulting Haar comparison on small compact open subgroups. The result here compares additive Haar in the Lie algebra and additive Haar in the `g − 1` coordinates.
