# Finite relative powers of an abelian scheme and their factor maps

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p. 98 (one-based PDF p. 106), writes
\(\pi_m : A^m \to X_U\) for the \(m\)-fold self-product of the universal
abelian variety over \(X_U\), and \([2]_x\) for the endomorphism of
\(A^m\) given by multiplication by 2 on the \(x\)-th factor. The
idempotents of that page are built from these maps and from the
symmetric group acting on the factors. The book is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
This module constructs these maps for an arbitrary abelian scheme
`A : AbelianScheme S`, in any universe; it uses no property of Shimura
varieties.

## The power and its projections

`relativePower A m` is an object of `Over S`. At exponent zero it is
`Over.mk (𝟙 S)`, the terminal object; at `m + 1` it is the binary
product `A.X ⨯ relativePower A m` in `Over S`, that is the fibre product
over `S`. `relativePowerProjection A m j` is the projection to the
factor `j : Fin m`, and `relativePowerLift A m f` is the map from `Z`
with projections `f j`. The equation `relativePowerLift_projection` and
the extensionality theorem `relativePower_hom_ext` give
`relativePowerIsProduct`: the fan of projections is a limit, so the
power is the product of `m` copies of `A.X` in `Over S`.

`relativePower_smooth_proper` proves that the structure map
`(relativePower A m).hom` is smooth and proper. The exponent zero case
is the identity. In the inductive step the first projection of the
fibre product is a base change of the structure map of the power, hence
smooth and proper, and the structure map of the product is its
composite with the structure map of `A.X`.

## Multiplication on one factor

`relativePowerMultiply A m i a` is the map in `Over S` whose projection
to the factor `i` is the projection followed by the scheme map of
`multiplication A a`, multiplication by the integer `a` in the group
law of `A`, and whose other projections are unchanged
(`relativePowerMultiply_projection`). On sections it raises the
coordinate `i` to the power `a` in the group of sections
(`relativePowerMultiply_points`). Multiplication by `1` is the identity
(`relativePowerMultiply_one`), multiplication by `a` and then by `b` on
the same factor is multiplication by `a * b`
(`relativePowerMultiply_comp`), and multiplications on two factors by
the same integer commute (`relativePowerMultiply_comm`).

`relativePowerDouble A m i` is `relativePowerMultiply A m i 2`, the map
\([2]_i\) of the source; `relativePowerDouble_projection` is its formula
on projections.

## Permutation of the factors

For `σ : Equiv.Perm (Fin m)`, `relativePowerPermute A m σ` is the map
whose projection to the factor `j` is the projection to the factor
`σ j` (`relativePowerPermute_projection`). The identity permutation
gives the identity (`relativePowerPermute_one`), and
`relativePowerPermute_comp` proves that the map of `σ` followed by the
map of `τ` is the map of `σ * τ`, with Mathlib's product of
permutations (`(σ * τ) j = σ (τ j)`). Thus these maps form a right
action of the symmetric group on the power, and the induced
contravariant maps on cohomology form a left action.
`relativePowerPermute_multiply` proves that the map of `σ` followed by
multiplication on the factor `i` equals multiplication on the factor
`σ i` followed by the map of `σ`.

All maps are morphisms in `Over S`, so they commute with the structure
map to `S`.
