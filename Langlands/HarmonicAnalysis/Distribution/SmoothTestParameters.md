# Jointly smooth families with fixed compact test support

A jointly smooth family whose slices have a common compact support
defines a continuous map from the parameter subset to the space
of smooth tests with that support. The linear chain rule after
translation expresses each iterated derivative of a slice as the
restriction of the corresponding joint derivative to the slice
directions. These derivative profiles vary continuously in the
supremum norm on the common compact support. They vanish outside
that support, so the same continuity holds in the derivative
coordinates of the fixed-support test space.

The integral over \([0,1]\) of the first-coordinate derivative at
\((ut,x)\) is jointly smooth. It uses Mathlib's interval integral,
which vanishes identically for an incomplete target space. For a
complete target space it extends the time divided difference of
\(h(t,x)\) smoothly through \(t=0\). At zero it is the first-coordinate
derivative. Multiplying by \(t\) gives \(h(t,x)-h(0,x)\), by rescaling
the interval integral and applying the fundamental theorem of
calculus.

These internal constructions allow a difference quotient of a
family of tests to be evaluated continuously in the test topology.
