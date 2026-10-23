# Involutions and similitudes under repeated scalar extension

Author: Worker 57.

## Purpose and provenance

This internal construction supplies the algebraic comparison needed when a
unitary or similitude group is formed after changing its coefficient ring.
It derives from the existing `AlgebraInvolution`, its actual subgroups of units,
and Mathlib's tensor-tower linear equivalence. It invokes no external existence
or representability theorem. The algebra may be noncommutative.

The module does not construct a scheme isomorphism, assert smoothness or
reductivity, or construct a Shimura variety. Those are separate geometric
obligations. No finite-dimensionality, basis, faithful scalar action, field,
flatness, or nonzero-ring hypothesis is required here.

## Transport through an algebra equivalence

For a commutative ring `R`, two `R`-algebras `A`, `B`, involutions `σ`, `τ`,
and an algebra equivalence `e : A ≃ₐ[R] B`, assume
`e (σ a) = τ (e a)` for every `a`. The lemma `equiv_symm_involution` derives
the corresponding identity for `e.symm` by applying the injective map `e`.

`similitudesEquiv` sends `(g,c)` to `(e(g),c)` and has inverse given by
`e.symm`. These are the existing groups defined by `g σ(g) = c`, with an
explicit invertible scalar coordinate. The construction uses the existing
`AlgebraInvolution.map`, and proves both inverse laws on the two coordinates.
`similitudesEquiv_unit` and `similitudesEquiv_multiplier` identify the resulting
algebra unit and show that the multiplier is unchanged.

`unitaryEquiv` restricts the same map on units to the actual subgroups
`g σ(g) = 1`. Applying `e` or `e.symm` to this equality proves membership;
their inverse laws prove bijectivity. `unitaryEquiv_unit` gives its value.
`unitaryEquiv_inclusion` proves that transport commutes with the existing
unitary-to-similitude inclusion, whose multiplier is one.

## The tensor-tower equivalence

Let `R`, `S`, `T` be commutative rings, with compatible algebra structures
`R → S → T` and `R → T`, expressed by `IsScalarTower R S T`.
Let `A` be any `R`-algebra. The definition

`baseChangeTowerEquiv R S T A : T ⊗[R] A ≃ₐ[T] T ⊗[S] (S ⊗[R] A)`

is in the expansion direction. Its pure-tensor formula and inverse formula are

- `t ⊗ a ↦ t ⊗ (1 ⊗ a)`;
- `t ⊗ (s ⊗ a) ↦ (s • t) ⊗ a`.

The underlying linear equivalence is the inverse of
`TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A`.
`AlgEquiv.ofLinearEquiv` promotes it to an algebra equivalence: the image of
one is computed directly, and `LinearMap.map_mul_of_map_mul_tmul` reduces
multiplicativity to products of pure tensors. This avoids imposing
commutativity on `A`.

For an involution `σ` of `A` fixing `R`, `baseChangeTowerEquiv_involution`
proves that this equivalence intertwines `σ.baseChange T` and
`(σ.baseChange S).baseChange T`. Both involutions fix all final coefficients;
there is no conjugation of `S` or `T`. The proof is tensor induction, with the
pure-tensor case definitional and the addition case following from linearity.

`baseChangeTowerSimilitudes` and `baseChangeTowerUnitary` apply the preceding
transport constructions. Their `_unit` lemmas give the algebra-unit formula.
`baseChangeTowerSimilitudes_multiplier` preserves the scalar multiplier, and
`baseChangeTowerUnitary_inclusion` proves compatibility with inclusion.

## Naturality

Let `U` be another commutative `S`-algebra with a compatible `R`-action, and
let `f : T →ₐ[S] U`. The theorem `baseChangeTowerEquiv_naturality` states that
expanding after applying `changeCoefficients (f.restrictScalars R)` equals
applying `changeCoefficients f` to the expanded tensor. Tensor induction proves
the identity. The theorem `baseChangeTowerSimilitudes_naturality` upgrades it
to equality in the actual similitude group after applying the existing
`baseChangeMap` on both sides; the multiplier coordinates agree definitionally.

The coefficient carriers `T` and `U` share a universe in these naturality
statements, as required by the existing `CommAlgCat`-based group maps.
The initial rings and algebra may inhabit separate universes. Naturality of
a separately bundled unitary coefficient-map functor is not asserted here.
