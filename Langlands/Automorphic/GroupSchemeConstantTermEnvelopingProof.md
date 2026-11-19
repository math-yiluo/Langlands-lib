# Enveloping derivatives preserve vanishing parabolic constant terms

`adelicConstantTermEnveloping` proves
`AdelicConstantTermEnvelopingStatement` for a number field in any universe.
For each proper rational parabolic, it uses the compact rational quotient
of the published unipotent radical and the published normalized quotient measure.

## Real directional derivatives

Fix an adelic point `g` and a real tangent direction `X`. The smooth
left-invariant vector field determined by `X` has a local integral curve
`curve` through the identity at time zero. Set
`z(t) = g * ofInfinite (curve t)`. For a quotient point represented by `n`,
the constant-term integrand along this orbit is `f(n * z(t))`. The
archimedean slice of `f` at the finite component of `n * g` is smooth.
The chain rule along `curve` and the left-translation law for the
directional value identify the derivative at every nearby time as
`D_X f(n * z(t))`, where `D_X` is `finitePlotSmoothDifferentialAction`.
Surjectivity of the quotient projection gives this derivative at every
quotient point.

The integrand of a continuous rational function is jointly continuous
in the adelic point and the quotient point. Before descent it is the
composition of multiplication and evaluation. The product of the identity
with the open quotient projection is a quotient map, so continuity descends.
Apply this to `D_X f` and compose with the orbit on a smaller closed time
interval. The resulting derivative integrand is uniformly bounded on the
product of that interval and the compact quotient.

The bound is integrable for the finite quotient measure. Continuity supplies
the almost-everywhere strong measurability conditions, and compactness
supplies integrability of the original integrand at time zero.
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` identifies the derivative
of the integral at zero with the constant term of `D_X f` at `g`. The
integral is the constant term of `f` at `z(t)`, which vanishes by hypothesis.
Uniqueness of the derivative gives the desired zero.

## Enveloping action

The finite plot-smooth vectors with vanishing constant term form the kernel
of the compact constant-term linear map composed with the inclusion into
continuous rational functions. On a simple tensor `c ⊗ X`, the complex
differential is multiplication by `c` after `D_X`. The real-direction result
and tensor-product induction show that every complex tangent direction acts
within the kernel. The enveloping algebra is a quotient of the tensor algebra,
so tensor-algebra induction finishes the proof. Scalars act by scalar
multiplication, generators by the complex differential, and products and
sums by composition and addition. The published parabolic quotient and
measure supply the compactness, Borel structure, and finiteness used above.

## Provenance

The theorem proves the internal Library target used for the Lie algebra
action on cusp forms. Definitions 6.5.1 and 6.5.2 of Getz–Hahn give the
vanishing condition and the cuspidal module context. [Library statement](GroupSchemeConstantTermEnvelopingStatement.md), [Getz–Hahn](https://doi.org/10.1007/978-3-031-41153-3)
