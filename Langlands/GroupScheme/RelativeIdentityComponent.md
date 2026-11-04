# The all-test relative identity-component criterion

For an arbitrary base scheme `S` and an actual group scheme `G` over `S`, this
file defines membership in the relative identity component on every test scheme.
It also defines what it means for an actual open subgroup inclusion to represent
that membership condition.

## Definitions

For `s : S`, `RelativeIdentityComponent.residueFiber G s` is the actual
group scheme obtained by pulling `G` back along the canonical map
`Spec κ(s) → S`. Its group law is the law induced by group-scheme base change.
For an arbitrary `T : Over S` and `x : T → G.X`,
`RelativeIdentityComponent.residueFiberPoint G x s` is the pullback
`x_s : T_s → G_s` as a morphism over `Spec κ(s)`.

`InRelativeIdentityComponent G x` means that, for every `s : S`, the
topological image of `x_s` lies in the connected component of the identity
point of `G_s`. The connected component is the published
`IdentityComponent.identitySet`; its definition needs no smoothness or
affineness assumption. The test scheme can be nonreduced, nonaffine, or empty.
The condition uses the entire underlying image of each fibre morphism, rather
than just its rational points.

For an actual homomorphism `i : H → G` of group schemes over `S`,
`IsRelativeIdentityComponent G i` has two fields:

- The underlying scheme morphism of `i` is an open immersion.
- For every test scheme `T` over `S` and every `x : T → G.X`, there exists a
  morphism `y : T → H.X` with `y ≫ i = x` if and only if
  `InRelativeIdentityComponent G x`.

Thus the second field specifies the represented points by factorization through
the given open subgroup. These are scheme morphisms over the base; points on
`T` are not required to be homomorphisms of group schemes. An open immersion is
a monomorphism, so such a factorization, when it exists, is unique.

`InRelativeIdentityComponent.precomp` proves that membership is preserved by
every morphism of test schemes. Pullback carries a composite to the composite
of the pulled-back maps; the image of this composite lies in the image of the
pulled-back original point. Applying its fibre-image hypothesis proves the
claim.

## Source and correspondence

J.-E. Bertin, SGA 3, Exposé VI_B, Definition 3.1 and special case 3.4, in the
Gille–Polo recomposed edition of 13 October 2024, PDF pp. 17–18, printed
pp. 347–348 (original margin pp. 341–342). Registered source:
`sga3-expose-vib-gille-polo-2024`, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.

Definition 3.1 defines `G⁰(T)` by the images of `T_s → G_s` lying in the
neutral connected components for every point `s` of the base.
`InRelativeIdentityComponent` is this criterion for an actual group scheme;
the source's representability assumption on fibres holds here because each
fibre is an actual pullback scheme. Special case 3.4 says that when the union
of these components is open, the induced open subscheme represents this
criterion. `IsRelativeIdentityComponent` records an actual open subgroup and
this all-test representation property. It does not assert that the union is
open or that such a subgroup exists.

The full official one-page Tome I errata of 13 October 2024 was read:
`sga3-tome1-errata-gille-polo-2024`, SHA-256
`e17b90eac75b25f53b5a6f7be84450b71c2f0d7df98f5c9f4ad4cb8e9038cea7`.
It has no correction to these passages. The restriction lemma is an internal
consequence of this definition and functoriality of actual pullback.

## Scope and remaining obligations

The universe `u` is arbitrary and shared by the base, group schemes, residue
fields and test schemes. There are no smoothness, affineness, finite
presentation, separation, connectedness, or field assumptions on the base
or the supplied group schemes.

This unit supplies the membership and representation predicates and their
restriction law. It does not construct a relative identity-component subgroup
or a subgroup functor, or prove existence, normality, openness of the union,
arbitrary-base-change compatibility, connectedness of fibres, closedness,
affineness, or a DVR specialization. Those results require separate statements
and proofs with their actual hypotheses.
