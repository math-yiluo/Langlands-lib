# Zero detection for a flat tensor coaction

This is an internal algebraic lemma for the Serre criterion proof. Let
`A` and `B` be commutative rings, let `B` be a flat `A`-algebra, and let
`M` be an `A`-module. Their universes are independent. Write
`η(m) = 1 ⊗ m`, defined as the linear map `tensorCoactionUnit`. Suppose an `A`-linear injection
`δ : M → B ⊗[A] M` satisfies

`(B ⊗ δ)(δ(m)) = (B ⊗ η)(δ(m))`.

If the only element with `δ(m) = η(m)` is zero, the map `δ − η` is
injective: equality of its values makes the difference a fixed element.
Flatness makes `B ⊗ (δ − η)` injective. The displayed identity puts
`δ(m)` in its kernel, so `δ(m) = 0` for every `m`. Injectivity of `δ`
then makes `M` subsingleton. Taking the contrapositive proves the
existence of a nonzero fixed element whenever `M` is nontrivial.

The proof directly uses Mathlib's preservation of injective linear maps
under tensoring with a flat module. No faithful flatness, module
finiteness, exactness of invariants, or geometric quotient theorem is
assumed. This derived lemma translates no new literature statement.
It does not construct `δ` from a published groupoid coaction or prove
its displayed identity; those remain separate adapter obligations.
