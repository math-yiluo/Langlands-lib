# Base change and descent fixedness of actual rational characters

For a group scheme `G` over any base scheme `B` and any base morphism
`b : S → B`, `rationalCharacters.baseChange` pulls back the actual character
morphism and composes it with the canonical identification of the pullback
of the multiplicative group with `Gm` over `S`. This is an additive map on
rational characters. On every relative test scheme, its value is exactly
the value of the original character at the point identified by
`baseChangePointsEquiv`.

The evaluation identity proves additivity and compatibility with restriction
along every actual group-scheme morphism. For a commutative group scheme,
base change followed by restriction to its actual character lattice agrees
with restriction followed by the existing lattice base change.

If `a : S → S` satisfies `a ≫ b = b`, every character pulled back from `B`
is fixed by the existing canonical descent transport. The proof evaluates
transport on all points. The transported point represents the same point
over `B`, through the canonical descent test isomorphism. Naturality of
character evaluation then reduces the equality to pullback of units along
an identity map on the underlying test scheme.

The lattice version follows by the definitional identification with rational
characters of a commutative group scheme. For any commutative algebra
extension `K/k`, its specialization says that every base-changed character
is fixed by the existing action of each `k`-algebra automorphism of `K`.
No field, finiteness, Galois, torus, affineness, smoothness or density
hypothesis is required for these results.

This is derived internal content from the actual pullback functor,
`Gm.baseChangeIso`, rational-character evaluation and restriction, and
the canonical point and character transport in `Torus/LatticeGalois`.
It does not descend an arbitrary invariant character, nor identify the
Lie determinant character of a base-changed action with the base change
of the original determinant character.
