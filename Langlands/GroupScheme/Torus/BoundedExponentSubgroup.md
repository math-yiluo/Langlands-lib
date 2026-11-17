# Closed subgroups of bounded exponent in groups of multiplicative type

This module supplies a finiteness step used in the proof of
`MultiplicativeTypeFiniteSubgroupSpreadingStatement`.

The main instance construction is
`Langlands.GroupScheme.RelativeMultiplicativeType.IsMultiplicativeType.isFinite_closedSubgroup_of_uniformPower`.
For a scheme `S`, a group scheme `H` of multiplicative type, a closed
subgroup inclusion `i : K ⟶ H`, and an integer `n > 0`, assume that
`x ^ n = 1` for every point `x : T ⟶ K.X` over every `S`-scheme `T`.
It returns the `IsFinite K.X.hom` instance. The definition is reducible
for typeclass use, following the same Library pattern as
`AffineCoordinates.algebraFiniteType`. No flatness, finite presentation, quasi-compactness,
or quasi-separatedness assumption is added on `K`. Finite type follows
from the closed immersion and the finite-type split ambient model.

The algebraic lemma `finite_of_span_groupLike_of_uniformPower` works over
any commutative ring `R`, with an independently sized commutative Hopf
algebra `A` of finite type. It assumes that group-like elements span `A`
as an `R`-module and that the convolution `n`-th power of the identity
algebra map is the convolution unit. Evaluating this identity at a
group-like element gives `g ^ n = 1`, by `convPow_apply_groupLike`.
Each such element is integral over `R`. The integral elements form an
`R`-submodule, so span induction proves that all of `A` is integral.
An integral finite-type algebra is finite as a module.

For a closed subgroup of a diagonalizable group over `Spec R`,
`Diagonalizable.span_groupLike_of_closedSubgroup` gives the spanning
hypothesis on its actual affine coordinate Hopf algebra.
`AffineCoordinates.algebraFiniteType` gives finite type. The universal
point of the subgroup transports along `AffineCoordinates.hopfSpecIso`
to the identity point of the coordinate spectrum. The pointwise power
hypothesis and Mathlib's multiplicative equivalence `Spec.mapMulEquiv`
therefore give the required convolution identity. Module finiteness
is converted to finiteness of the spectrum structure morphism and then
transported back along the coordinate isomorphism.

`uniformPower_baseChange` transports the power hypothesis by the
published multiplicative equivalence on points after base change.
An affine cover reduces the split case over any scheme to the ring
case. An actual diagonalizable presentation transports the ambient
inclusion. Finally finiteness descends from the fppf splitting cover
in the definition of `IsMultiplicativeType`, using the published fppf
locality of finite morphisms.

This is derived internal content: it combines the published actual
coordinate and subgroup constructions with standard integrality,
affine locality, and finite-morphism descent. It proves a consequence
of a supplied uniform exponent. It does not prove existence or
spreading of that exponent, local quasi-finiteness near a finite fibre,
trivial-fibre spreading, or the complete target statement.
