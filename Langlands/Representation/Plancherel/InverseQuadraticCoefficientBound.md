# Bounded inverse quadratic coefficients detected by a fixed functional

This derived helper takes a rational continued operator, one fixed input vector, and a positive algebraic inner-product core on its target. Its `inverseQuadraticCoefficient` is the reciprocal of the core's diagonal value on the continued image. If one fixed linear functional takes a constant nonzero value on that image throughout the operator's regular region, the inverse quadratic coefficient is uniformly bounded there by a positive real constant.

The finite polynomial numerator range estimate from `PolynomialPositiveFormBound` gives `norm(a)^2 ≤ C * inner(Tv,Tv).re`. Hermitian symmetry identifies the diagonal with its real part. The fixed nonzero value forces that real part to be positive, and elementary division yields the uniform bound `C / norm(a)^2` for the inverse diagonal. The ambient representation carrier need not be finite dimensional and has no prechosen topology. Parameter compactness is not used.

This is an analytic bound for the quadratic coefficient only. In a unitary scalar application an adjunction identity identifies the reciprocal scalar with a fixed source quadratic value times this inverse coefficient. No pole-support or rational-function regularity assertion is made here.

The real-diagonal identity uses `CornerFormGluing.inner_self_eq_ofReal_re`.
