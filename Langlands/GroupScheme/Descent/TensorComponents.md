# Actual scheme components from a finite tensor decomposition

Let `k` and `L` be fields in arbitrary universe `u`, with a specified
`k`-algebra structure on `L`, and let `I : Type` be a finite indexing type.
The actual extension map is `fieldMap k L : Spec L → Spec k`.

Given an actual `L`-algebra equivalence
`e : L ⊗[k] L ≃ₐ[L] (I → L)`, `tensorComponent e i` is the map from
`Spec L` into the actual double overlap obtained from evaluation at `i`,
the equivalence `e`, and Mathlib's tensor-product/pullback comparison.
The canonical map from the coproduct of these components to the overlap
is an isomorphism. The proof factors it through Mathlib's finite
`sigmaSpec` isomorphism, the spectrum of `e`, and `pullbackSpecIso`.
The helper `finiteSigmaSpec_isIso` supplies a version with independent
index and ring universes. It constructs the Cartesian product ring fan
and proves its universal property using `RingHom.pi`. Passing its opposite
through `Scheme.Spec`, which preserves finite coproducts, identifies the
canonical `sigmaSpec` map with a colimit comparison isomorphism.

The first structural projection is the identity: this follows from the
`L`-algebra condition on `e`, with the first tensor factor supplying the
source's `L`-algebra structure. If specified `k`-algebra automorphisms `s i`
satisfy `e (a ⊗ b) i = a * s i b`, the second projection is exactly
`Spec (s i)`. Both projections are therefore isomorphisms.

This is an internal deduction from Mathlib's actual affine pullback and
finite coproduct constructions. The tensor equivalence and its displayed
formula are inputs; this module neither proves nor assumes their
unconditional existence for an arbitrary extension. The finite Galois
algebra decomposition is a separate prerequisite. No perfectness or
characteristic restriction is used.
