# Top integrals of actual positively weighted Frobenius kernels

This derived construction works over any field `k`, in exponential characteristic
`p`, at any natural height `r`. Let `G` be an actual affine group scheme over
`Spec k`. Its genuine coordinate algebra is `C = CharacterUnits.Coord G`, its
Frobenius augmentation quotient is `Q = quotientAlgebra G p r`, and
`DistributionAlgebra p r` is the full linear dual of `Q` with convolution from the
original coordinate coproduct. The convolution counit on this dual is evaluation
on `1 : Q`.

For the explicit construction assume an action `b` of a split torus `S` on `G`, a
cocharacter `ν`, and a finite family of actual coordinate functions `t i` with
characters `w i`. Evaluation at `t` must be bijective as an algebra homomorphism
from the polynomial algebra, each `t i` must be a weight eigenfunction vanishing
at the group identity, and every pairing `⟨w i, ν⟩` must be strictly positive.
These are hypotheses on original coordinates and actions. The construction does
not require an ordering or additive root-subgroup parametrization.

## Construction and identities

`polynomialCoordinates` is the inverse of evaluation at `t`.
`polynomialCoordinates_origin` identifies its constant coefficient with actual
identity evaluation. The existing `polynomialModelEquiv` therefore identifies
`Q` with the polynomial quotient retaining exponents `a ≤ N`, where every
component of `N = bound p d r` is `p^r - 1`. `quotientBasis` transports the
retained coefficient equivalence to a basis of `Q`, and
`quotientBasis_apply` identifies its elements with the original monomial classes.

`topDistribution` is coefficient extraction at `N` through that genuine quotient
equivalence, wrapped as an element of the convolution dual. Its value on the
class of an original coordinate is exactly that coordinate polynomial's top
coefficient. Evaluating it on the class of the monomial `N` gives `1`, proving
`topDistribution_ne_zero`.

Write `z` for this top distribution. The main identities are, for every element
`ell` of the full distribution algebra,

```
z * ell = ell.ofConv 1 • z
ell * z = ell.ofConv 1 • z.
```

They are `top_mul` and `mul_top`. In particular this is a nonzero two-sided
integral in the actual convolution algebra; no product of independently
translated axes or commutation of different root subgroups is assumed.

## Implemented proof

The original torus character grading and injectivity of evaluation show that a
homogeneous original coordinate has a weighted homogeneous polynomial.
Consequently `z` vanishes on a homogeneous coordinate unless its height is
`H = ⟨weight w N, ν⟩`. Positivity of all variable heights also shows that any
homogeneous coordinate of nonpositive height is scalar. Thus every `ell` with
`ell(1) = 0` kills all such coordinates after quotienting.

`coordinateContraction` applies the quotient map in both tensor factors and
contracts by two distributions. The existing original-coordinate theorem
`coordComul_mem_iSup` places the coproduct of a coordinate of character `χ` in
the sum of tensor weight spaces of characters `α` and `χ - α`. If the height of
`χ` is at most `H`, a contraction by `z` and an `ell` vanishing on `1` is zero:
either the factor paired with `z` has height different from `H`, or the other
factor has nonpositive height and is killed by `ell`. The same argument applies
in the opposite factor order. Submodule kernel containment makes this argument
apply to the full tensor sum.

Each retained monomial has height at most `H`. Equality on `quotientBasis` and
the genuine quotient coproduct identity therefore give `z * ell = ell * z = 0`
whenever `ell(1) = 0`. Subtracting `ell(1)` times the convolution unit proves the
two displayed identities for arbitrary distributions.

`exists_nonzero_twoSidedIntegral` assumes instead that `G` is smooth and locally
of finite type and that every augmentation weight of the split-torus action
pairs positively with `ν`. The existing theorem
`TorusUnipotence.exists_positiveWeight_coordinates`, valid in arbitrary
characteristic, supplies the coordinate family used above. This proves
existence of a nonzero two-sided integral for every `r` under those hypotheses.
The statement includes empty coordinate families, height zero and exponential
characteristic one; the same proof handles their one-dimensional quotients.

## Provenance and scope

This is derived infrastructure from the Library's actual Frobenius quotient,
polynomial-box equivalence, original torus character grading and positive-weight
coordinate theorem. The argument above is the implemented proof and is not
attributed to an additional literature theorem. It proves neither uniqueness of
integrals nor nondegeneracy of convolution pairings. It does not construct a
Steinberg module, identify a highest-weight vector, bound the whole covariant
induced space, or prove `SteinbergBigCellStatement`.
