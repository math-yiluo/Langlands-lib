# Fixed geometric components under purely inseparable extension

This unit constructs an equivalence between the full Galois-fixed geometric
component groups of an actual smooth affine group scheme and its pullback
along a purely inseparable field extension. Its forward homomorphism is
`geometricComponentCanonicalBaseChange`. The construction requires no
supplied embedding of the chosen algebraic closures.

All declarations are in `Langlands.GroupScheme.IdentityComponent`.

## Scope and carriers

Let `k K : Type u` be fields with `Algebra k K` and
`IsPurelyInseparable k K`. Let
`H : GroupScheme (Spec (CommRingCat.of k))`, with
`Smooth H.X.hom` and `IsAffineHom H.X.hom`.
Here `GroupScheme` is the existing group-object architecture over schemes,
and `baseChanged k K H` is its actual pullback along `baseMap k K`.

`GeometricComponents k H` is the group of connected components of the
actual pullback of `H` to `AlgebraicClosure k`.
`geometricComponentFixedSubgroup k H` consists of the components fixed by
every element of `Field.absoluteGaloisGroup k`.
The source of the equivalence is this entire fixed subgroup; its target is
`geometricComponentFixedSubgroup K (baseChanged k K H)`.

The extension may be infinite; there is no finite-degree or uniform
inseparability-exponent hypothesis. There is no assumption of perfection,
characteristic zero, connectedness, reductivity, commutativity or the
existence of rational representatives of fixed components. Both fields
and their chosen closures are in the same universe.

## Construction and intrinsic laws

With compatible algebra structures
`Algebra (AlgebraicClosure k) (AlgebraicClosure K)` and
`IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K)`, the theorem
`geometricComponentBaseChangeEquiv_purelyInseparable_mem_fixed_iff`
states, for every `c : GeometricComponents k H`,

```text
geometricComponentBaseChangeEquiv k K H c is fixed over K
  if and only if c is fixed over k.
```

These supplied closure structures occur only in this fixedness comparison.
`geometricComponentCanonicalBaseChange_purelyInseparable_surjective`
proves surjectivity of the published canonical homomorphism, whose
definition already makes its value independent of the closure embedding.
The registered construction is

```text
geometricComponentFixedPurelyInseparableEquiv k K H :
  geometricComponentFixedSubgroup k H ≃*
    geometricComponentFixedSubgroup K (baseChanged k K H).
```

It is `MulEquiv.ofBijective` applied to that canonical homomorphism,
using its published injectivity and the surjectivity proved here.
`geometricComponentFixedPurelyInseparableEquiv_apply` identifies its
forward value with canonical extension, and
`geometricComponentFixedPurelyInseparableEquiv_toMonoidHom` gives the
equality of homomorphisms.

For every `k`-algebra embedding
`i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K` and every fixed target
component `d`,
`geometricComponentFixedPurelyInseparableEquiv_symm_val` computes the
underlying component of the inverse as

```text
((geometricComponentFixedPurelyInseparableEquiv k K H).symm d).val
  = (geometricComponentBaseChangeEquivOfEmbedding k K H i).symm d.val.
```

Thus any such embedding computes the inverse of the same canonical
equivalence. Finally,
`geometricComponentFixedPurelyInseparableEquiv_naturality` states that
the equivalence commutes with `geometricComponentFixedMap` for every
actual group-scheme homomorphism `f : H ⟶ H'`, where `H'` satisfies the
same smoothness and affineness hypotheses. The map over `K` is induced
by the actual pullback of `f`.

## Implemented derivation and provenance

This is a derived construction from the published component comparisons
and pinned Mathlib field theory, with no new external structural input.
The private helper
`galoisRestriction_surjective_of_purelyInseparable` proves surjectivity
of `Field.absoluteGaloisGroup.mapOfAlgebra k K` through compatible
closures. Pure inseparability implies algebraicity of `K/k`;
transitivity with the algebraic closure of `K` makes that closure an
algebraic closure of `k` as well.

For a source closure automorphism `σ`, Mathlib's `AlgEquiv.liftNormal`
provides a `k`-algebra automorphism `τ` of `AlgebraicClosure K` extending
it. Mathlib's `instSubsingletonAlgHomOfIsPurelyInseparable` identifies
the two `k`-algebra homomorphisms from `K` to this field: its structural
embedding and its composition with `τ`. Therefore `τ` fixes `K` and
defines an element of `Field.absoluteGaloisGroup K`.
`AlgEquiv.restrict_liftNormal` verifies that its restriction is `σ`.
This argument uses no degree or exponent bound.

The published
`geometricComponentBaseChangeEquiv_restrict_smul` expresses
equivariance for this actual restriction. To reflect fixedness, lift
an arbitrary source Galois element, apply equivariance and use
injectivity of the geometric component equivalence.
Preservation is the property of
`geometricComponentFixedBaseChange`.

For canonical surjectivity, choose a closure embedding internally,
take the inverse image of a fixed target component under
`geometricComponentBaseChangeEquiv`, and apply the fixedness
equivalence. The published
`geometricComponentCanonicalBaseChange_eq` identifies its forward
image with the desired target. The inverse-value formula follows
from the canonical value formula at any embedding and the inverse
laws of multiplicative equivalences. Naturality is the published
canonical naturality theorem after unfolding the forward map.

This unit does not construct a component-group scheme or a sheaf
quotient. It does not assert surjectivity for arbitrary field
extensions or descend fixed components to rational points.
