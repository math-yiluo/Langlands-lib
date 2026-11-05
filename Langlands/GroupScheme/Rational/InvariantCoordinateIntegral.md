# Normalized invariant integration on actual affine group coordinates

This internal interface uses `Lie.coordinateAlgebra H`, the actual coordinate
algebra of the supplied affine group scheme `H`. It introduces the universal
point over `A ⊗[k] k[H]` and the pullback of left translation by each actual
`A`-point. It proves that translation fixes constant points and sends the
universal point to its left translate. Maps of coefficient algebras preserve
the universal point.

A linear functional on `k[H]` extends by tensor product to an `A`-linear
contraction `A ⊗[k] k[H] → A`. Contraction is natural in `A`.
`InvariantIntegral H` consists of a linear functional taking `1` to `1` and
invariant under the actual left-translation pullbacks on every coefficient
algebra. It asserts no existence theorem for reductive groups.

The construction is an internal generalization of the exponent-zero Laurent
coefficient used in `Rational.SplitTorusVectorExtension`: the tensor coordinate
factor replaces the Laurent variable, and a normalized invariant functional
replaces extraction of its exponent-zero coefficient. All translation maps are
defined through the existing actual affine-point coordinate equivalence.
