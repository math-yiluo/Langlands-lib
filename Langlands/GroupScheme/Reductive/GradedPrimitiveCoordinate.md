# Primitive coordinates on a positively graded affine line

Let `R` be any commutative ring, `F` a group-valued functor on commutative
`R`-algebras corepresented by `B`, and `A` an `R`-algebra. This module constructs
supported orbit points and a dual-number coefficient map, then proves the
following internal additivity criterion. Suppose:

- `c : B → B[T,T⁻¹]` is an `R`-algebra grading in the sense of
  `GradedLine.IsGrading`;
- `x ∈ B` is homogeneous of positive natural degree `d`, and evaluation
  `R[X] → B` at `x` is surjective;
- there is a group homomorphism `hat : F(A) → F(A[T,T⁻¹])` whose classifying
  coordinate on each `b ∈ B` is obtained from `c(b)` by applying the
  classifying map of the original point to each coefficient.

Then `coord_mul_of_homogeneous_generator` proves
`coord(y*y')(x) = coord(y)(x) + coord(y')(x)` for all `y,y' ∈ F(A)`.
There is no reducedness, local-ring, flatness, characteristic, or
finite-generation assumption. Only surjectivity of polynomial evaluation
is needed in this criterion.

The additive submonoid `gapMonoid d` consists of zero and the integers at
least `d`. The subalgebra `gapAlgebra A d` consists of Laurent polynomials
supported in this submonoid. When `d > 0`, the constant coefficient of a
product is the product of the constant coefficients, and its degree-`d`
coefficient is the sum of the two products involving degrees `0` and `d`.
Thus `dualCoeffHom` sends `p` to `p₀ + ε p_d` in the dual numbers
`A[ε]/(ε²)` as an `R`-algebra map.

Polynomial induction proves that `c(b)` lies in the gap subalgebra for
every `b`, since `x` generates the algebra and is homogeneous of degree
`d`. The assumed orbit formula then lifts `hat(y)` to an `F`-point over
the gap subalgebra. Injectivity of points under a subalgebra inclusion
makes this lifting a group homomorphism, `supportedPoint`.

Composing `supportedPoint` with `dualCoeffHom` gives a group homomorphism
`ζ : F(A) → F(A[ε]/(ε²))`. Homogeneity gives
`coord(ζ(y))(x) = ε coord(y)(x)`. At `y=1`, taking constant coefficients
proves that the identity point has `x`-coordinate zero. Because `x`
generates `B`, equality of its coordinate determines a point, so each
`ζ(y)` reduces to the identity modulo `ε`. The published arbitrary-base
lemma `Corepresented.snd_coord_mul` now makes their infinitesimal coordinates
add. Multiplicativity of `ζ` proves the criterion.

This is derived internal content: it adapts the supported-subalgebra and
dual-number argument of `Rational.TorusWeightPrimitive` to an integer grading,
using the grading interface from `CommutativeAlgebra.GradedLineLocal`.
It does not construct the required multiplicative orbit map for a dynamic
root group, assert torus equivariance, or prove the local isomorphism theorem.
