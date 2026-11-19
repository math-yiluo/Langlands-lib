# Groups of exponent `p` over a perfect closure

`Langlands.GroupScheme.exponentVectorGroupForm` proves the published
`Langlands.GroupScheme.ExponentVectorGroupFormStatement.{u}`. After base
change to a perfect closure, the given group is isomorphic to a standard
vector group over that closure. The proof follows Corollary 14.56 of J. S.
Milne, *Algebraic Groups* (2017), printed p. 297, registered as
`milne-2017-algebraic-groups`.

Let `H` be the base change of `G` to `K`. The injective field map `k → K`
gives `CharP K p`. The structure map of `H` is a pullback projection, so it
is smooth and affine. The monoidal pullback preserves commutativity.
`connectedSpace_baseChange_of_smooth_affine` gives connectedness of `H` by
geometric connectedness of `G`, which applies to every field extension.

`HasUniformPowerExponent.baseChange` transfers the law `g ^ p = 1` to all
scheme tests over `Spec K`. It uses `baseChangePointsEquiv`, which identifies
the group of `T`-points of `H` with the points of `G` on the same test scheme
viewed over `Spec k`.

Apply `perfectFieldExponentVectorGroup`, the Library proof of Milne's
Proposition 14.54, to `H` over `K`. It gives the rank and the group-scheme
isomorphism over `Spec K`.
