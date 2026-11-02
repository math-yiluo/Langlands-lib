# Tensor norm naturality

This internal, derived module proves compatibility of the determinant norm with
an arbitrary map of the tensor coefficient algebra. For commutative
`A`-algebras `B`, `S`, and `T` in one universe, a finite basis `b` of `B/A`
and an `A`-algebra map `g : S → T`, the formula is
`N_T((g ⊗ id_B)(x)) = g(N_S(x))` for `x ∈ S ⊗_A B`.
No injectivity, reducedness, or field assumption is imposed on `S`, `T`, or `g`.

The proof uses Mathlib's determinant definition `Algebra.norm`. It proves
that the left multiplication matrices in the bases `b.baseChange S` and
`b.baseChange T` are related entrywise by `g`, by tensor induction, then uses
compatibility of the determinant with a ring map. This is an internal
algebraic prerequisite for morphisms of the actual Weil-restricted
multiplicative group, derived directly from the determinant construction.

The additional API `tensorNorm A B S` defines the norm on `B ⊗_A S` by
swapping the factors before applying `Algebra.norm S`. Its naturality and
scalar formula assume that `B/A` is finite free; the scalar formula has
exponent `Module.finrank A B`. The proof uses a chosen finite basis only
internally, so the construction does not depend on a basis parameter. The
zero coefficient ring is included by a subsingleton case.

`tensorNormUnits` is the induced homomorphism on units.
`tensorNormUnits_naturality` is the corresponding arbitrary-map formula,
and `tensorNormUnits_scalar` identifies the norm of a scalar unit with its
rank power. These follow by equality of the underlying unit values.

Author: Worker 207.
