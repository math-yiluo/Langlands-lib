# Tori in actual Lie-element centralizers

For a homomorphism `i : T → G` from a commutative group scheme over any
commutative ring `R`, every point of `T` centralizes every actual tangent
vector in the image of `Lie.targetMap i R`. The proof restricts to each
affine refinement, extends the tangent vector to its coefficient algebra,
uses commutativity in `T` on the dual-number test, and postcomposes the
commutation equation by `i`. It therefore proves inclusion of all-test
subgroup functors, without a smoothness, representability, or splitting
hypothesis.

Given a representative `j : C → G` of the Lie-element centralizer,
`Lie.elementCentralizerTorusFactor j hrep i hX` is the canonical group
homomorphism `T → C` furnished by that containment and the representative's
universal property. Its composite with `j` is `i`, as proved by
`Lie.elementCentralizerTorusFactor_comp`. Despite its name, this construction
works for any commutative group scheme `T`; it does not require a torus.

The maximality theorem assumes a closed representative `j : C → G` of the
Lie-element centralizer, with `C` smooth and affine. If `i : T → C⁰` is a
maximal torus and `X` is in the tangent image of `T → C⁰ → C → G`, then the
same composite is a maximal torus in `G`. Indeed, every containing torus
also has `X` in its tangent image and hence factors through `C`. Its source
is connected, including when it is nonsplit, so it factors through `C⁰`.
Closedness descends to this factor. Maximality in `C⁰` now makes the original
map into the containing torus an isomorphism.

This is a derived elementary step in the proof of Milne, *Algebraic Groups*
(2017), Proposition 17.90, printed p.381 / PDF p.397. It does not assert that
a semisimple tangent vector belongs to the Lie algebra of a maximal torus,
or that its centralizer is representable or smooth. Those remain structural
inputs for Proposition 17.90 and the Cartan generation theorem.
