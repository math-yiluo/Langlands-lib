# Galois descent and norms over arbitrary test algebras

This is an internal construction from the Library's actual affine-point and
coordinate interfaces and Mathlib's finite Galois fixed-field theorem. It
extends the field-point constructions in `GaloisPointDescent` and
`GaloisPointNorm` to every commutative test algebra. It does not rely on a
structural theorem about tori or unipotence.

Fix fields `k` and `K` in an arbitrary common universe, an algebra structure
`k → K`, and a commutative `k`-algebra `A` in that universe. No nontriviality,
finite generation, reducedness, or flatness hypothesis on `A` is imposed.
Flatness over the field is supplied by the existing instance.

## Fixed tensors

`coefficientConjugate` acts on `K ⊗[k] A` by applying a `k`-automorphism of
`K` to the first tensor factor and fixing the second. Its identity and
composition laws agree with multiplication in the automorphism group.

For finite Galois `K/k`, `mem_range_includeRight_iff` proves that a tensor is
fixed by every such automorphism exactly when it lies in the image of
`A → K ⊗[k] A`, `a ↦ 1 ⊗ a`. The proof chooses a possibly infinite `k`-basis
of `A` and uses its scalar extension to `K`. Conjugation applies to each basis
coefficient. The finite Galois fixed-field theorem puts every fixed coefficient
in `k`, and the finite support of the tensor's basis representation reconstructs
its preimage in `A`.

## Actual affine points

For a group scheme `G` over `Spec k`, `conjugate` and `extend` apply the
corresponding algebra maps to actual affine points. The subgroup
`fixedSubgroup` consists of the tensor-valued points fixed by every conjugation.
When `G` is affine, `extend_injective` follows from injectivity of
`includeRight` and of coefficient extension on affine coordinates.

For finite Galois `K/k`, `exists_extend_eq` applies the fixed-tensor theorem to
each coordinate of a fixed point. The existing
`CocharacterDatum.exists_affineMap_eq` reconstructs an actual point over `A`.
The chosen point `descend` satisfies `extend_descend`, and injectivity supplies
both inverse laws of the multiplicative equivalence `fixedEquiv` between
`G(A)` and the fixed subgroup of `G(K ⊗[k] A)`. `mem_range_extend_iff`
characterizes the same image. These descent statements allow noncommutative
`G` and require no smoothness or finite type hypothesis.

## Norm and naturality

For a commutative group scheme `Z`, `conjugateProduct` multiplies all
conjugates of a tensor-valued point. Commutativity makes this a group
homomorphism. Left multiplication permutes the finite automorphism group,
so `conjugateProduct_fixed` proves the product is fixed. If `Z` is affine and
`K/k` is finite Galois, `norm` applies the inverse of `fixedEquiv` to this
product, giving a homomorphism `Z(K ⊗[k] A) → Z(A)`.

`extend_norm` identifies its coefficient extension with the original product
of conjugates. `norm_extend` identifies the norm of an extended point with
its power by `Module.finrank k K`, using the Galois automorphism count.

`tensorMap` changes the test-algebra factor. It commutes with conjugation,
and `extend_naturality` and `conjugate_naturality` express these identities on
actual points. They require no finite Galois or affineness premise.
`norm_naturality` proves that the norm commutes with every `k`-algebra map
`A → B`, by comparing coefficient extensions and products of conjugates.
`norm_target_naturality` proves that every actual homomorphism between affine
commutative group schemes commutes with the norm, using naturality of the
existing affine-point target maps.

This module supplies a point norm natural in all test algebras. It does not yet
construct a morphism from a Weil restriction, prove that such a morphism detects
a nonzero cocharacter, or prove `NoTorusUnipotentStatement`.
