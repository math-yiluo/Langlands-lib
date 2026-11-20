# Polynomial fixed points with spectral bounds

Author: Worker 786.

The fixed-point lemma is an internal construction for the nearby-lift
argument of Berkovich, *Vanishing cycles for formal schemes* (1994), §7,
especially Lemma 7.3. It supplies the spectral bound on the displacement in a
polynomial equation written as a fixed-point equation.

First the proof works in a complete ultrametric normed ring. The difference
of two powers of degree `d + 1` on the closed ball of radius `r` has norm
bounded by `r ^ d` times the distance between the arguments. The
ultrametric inequality preserves a common bound through the finite sum of
terms. The fixed-point map preserves the closed ball because its value at
zero lies in the ball and its Lipschitz constant is less than one. Banach's
fixed-point theorem supplies the solution there.

For the spectral version, use a free generalized Tate algebra with one
variable of radius `r` for the constant term. A variable for the coefficient
of degree `d + 1` has radius `q / r ^ d`, where `0 < q < 1`. The
norm calculation in this algebra gives the fixed point of the universal
equation. The spectral hypotheses on the actual coefficients give weighted
power bounds and hence a bounded specialization to the presented affinoid
algebra. Pullback of a point of its spectrum along the specialization
transfers the norm bound on the universal solution to the required
spectral bound.
