# Actual binary quaternion kernel

Authors: Worker 124.

This internal unit identifies the entire kernel scheme of the actual
binary quaternionic product action with the finite diagonalizable group
`μ₂`. It retains the nonreduced structure in characteristic two. The
construction uses the exact all-test kernel equation already proved in
`BinaryQuaternionGroupScheme`, the actual norm-square/scalar identities,
and the Library's represented-subgroup and diagonalizable group APIs.
It assumes no classification or comparison with a larger spin cover.

`TwoLattice` is a universe-compatible lift of the two-element additive
cyclic group. The actual group scheme `muTwo` is its diagonalizable
group. Evaluation of a character at the distinguished generator gives
a unit whose square is one. Conversely, `characterOfUnit` constructs
the character from such a unit, and `characterUnit_injective` proves
that its generator determines it. These statements hold over arbitrary
commutative rings.

In reduced degree two, a scalar unit of square one has reduced norm
one. Thus `scalarNormOne` and `characterProduct` give an actual point of
`SL₂(R) × SL₁(D)(R)` from a character, with coordinates the scalar
special-linear diagonal and the scalar quaternion unit. The full
kernel equation proves that this product lies in the action kernel.
Conversely, a kernel point has coordinates `(rI,scalar(r))`, with
`r*r = 1`. The unit with value and inverse both `r` constructs a
character whose product is exactly that original point. The diagonal
product is injective because its first matrix entry recovers the
generator value.

The all-test point comparisons transport `characterProduct` to
`diagonalPoints`. Character-point naturality and the actual coefficient
restriction maps prove its naturality, constructing the morphism
`diagonal : μ₂ → SL₂ × SL₁(D)`. Its pointwise injectivity proves
monicity of the underlying relative-scheme morphism. The two
coefficient-group implications prove equality of its represented
subgroup functor with the full kernel functor of `BinaryScheme.unitHom`.
The uniqueness of representing group schemes then constructs
`muTwoUnitKernelIso`, and its composite with the kernel inclusion is
exactly the original diagonal morphism.

The diagonalizable group of a finite character group is finite over
the base. Transport along this actual isomorphism proves
`unitKernel_isFinite`. Over an infinite ground field, the earlier
factorization into the published hyperbolic isometry group is
available. Its all-test kernel equation is the same, giving
`muTwoIsometryKernelIso` and `isometryKernel_isFinite`, with the same
inclusion compatibility. Every kernel point on every relative test is
accounted for; no smoothness or restriction on the characteristic is
imposed on the kernel.

This unit does not prove simple connectedness of the product source,
surjectivity onto the connected hyperbolic isometry group, a central
isogeny onto that group, or the comparison with an arbitrary supplied
larger spin cover. The host Kneser–Tits theorem remains open.
