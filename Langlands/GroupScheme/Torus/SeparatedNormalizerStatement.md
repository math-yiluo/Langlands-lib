# Smooth closed torus normalizers in separated smooth groups

`Langlands.GroupScheme.SeparatedTorusNormalizerStatement.{u}` is a
statement-only, `Prop`-valued definition. The module proves nothing and adds no
other declarations or axioms. It is a prerequisite of the proof of
[`SelfCentralizingTorusWeylAffinenessStatement`](SelfCentralizingWeylAffinenessStatement.md),
whose ambient group need not be affine over its base.

## Hypotheses and conclusion

The proposition quantifies over every scheme `S : Scheme.{u}` and every group
scheme `G : GroupScheme S` such that the structure morphism `G.X.hom` is
smooth, separated and quasi-compact. It does not assume that `G` is affine over
`S`, that its fibres are connected or affine, or anything about the base.

It then quantifies over a commutative group scheme `T : CommGroupScheme S` and a
homomorphism `t : T.toGrp ⟶ G` such that

- `RelativeTorus.IsTorus T.toGrp`: on some étale cover of `S`, every base change
  of `T` is a finite split torus, whose rank may vary between cover members;
- `IsClosedSubgroup t`: the underlying morphism of schemes `t.hom.hom.left` is a
  closed immersion.

The torus is not assumed maximal, self-centralizing or central.

The conclusion supplies a group scheme `N : GroupScheme S` and a homomorphism
`n : N ⟶ G` such that

1. `IsClosedSubgroup n`: the underlying morphism of schemes of `n` is a closed
   immersion;
2. `Smooth N.X.hom`: the normalizer is smooth over `S`;
3. `(torusNormalizer t).IsRepresentedBy n`: `n` is a monomorphism over `S`, and
   on every test scheme `U : Over S` a point of `G` factors through `n` exactly
   when it belongs to the published functor `torusNormalizer t`.

`torusNormalizer t` is the normalizer of the subgroup functor of points of `G`
coming from `T`, tested after every refinement: a point `g : U ⟶ G.X` belongs to
it when, for every `a : V ⟶ U` of schemes over `S`, conjugation by `a ≫ g` and by
its inverse sends every `V`-point coming from `T` to a `V`-point coming from `T`.
This is the scheme-theoretic normalizer functor `Norm_G(T)` of SGA 3, including
test schemes with nilpotents.

## Source correspondence

The primary source is A. Grothendieck, SGA 3, Exposé XI, *Critères de
représentabilité. Applications aux sous-groupes de type multiplicatif des
schémas en groupes affines*, Gille–Polo provisional recomposition
(5 December 2008), registered as `sga3-exposes-xi-xii-xiv-gille-polo-2008`
(file `Expo11.pdf`, SHA-256
`cdb58ea5518c29e998e12aea8d958e488c466c3b12fe2ed178a009758a553ead`),
printed p.111, original pp.167–168, one-based PDF p.27:

- Corollary 5.3 bis: for a subgroup `H` of multiplicative type of a smooth
  affine group `G` over `S`, the subgroup functor `Norm_G(H)` is representable
  by a closed subscheme of `G` which is smooth over `S`.
- Remark 5.6: for 5.2 and the first assertion of 5.3 the appeal to the
  representability theorem 4.2 may be replaced by the closed-transporter result
  of Exposé VIII, 6.4, so the hypothesis that `G` is affine is not needed there;
  the remark states that the same observations extend to the variants 5.2 bis
  and following, which include 5.3 bis.

This proposition is the case of 5.3 bis in which `H` is a closed relative torus
and the affineness hypothesis is removed according to Remark 5.6. It
additionally assumes that `G` is separated and quasi-compact over `S`. These
assumptions hold in the downstream application (`G` smooth, separated and
quasi-compact with connected affine residue fibres) and are retained to
describe exactly the class of groups needed there; the source does not require
them. A relative torus in the sense of `RelativeTorus.IsTorus` is of
multiplicative type, being étale-locally diagonalizable, so it is a subgroup of
multiplicative type in the sense of the source once `t` is a closed immersion.

In the special case where the torus is a maximal torus equal to its own
centralizer in a group with connected fibres, the same conclusion is also part
of M. Raynaud, SGA 3, Exposé XV, Proposition 7.1(iv), printed p.282 (original
p.446), one-based PDF p.50 of `Expo15.pdf`, registered as
`sga3-expose-xv-raynaud-2008` (SHA-256
`03647e0232067a7508bb1350e7aace3e88d58872956f068ced808a4f9cc3273f`).

The Library already proves the affine case: `RelativeTorus.closedNormalizer`
and `relativeTorusSmoothNormalizerModel` require `IsAffineHom G.X.hom`. This
statement asks for the non-affine generalization and asserts nothing about a
quotient by the normalizer or by the torus.
