# Birational group laws and their solutions

The module `Langlands.AlgebraicGeometry.BirationalGroupLaw` defines `S`-birational group
laws on a scheme `X` over a base `S`, and solutions of such laws, following Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §5.1 (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`). It contains definitions only.

## Density in fibres

BLR 2.5 (printed p. 55) calls an open subscheme `U` of an `S`-scheme `X` `S`-dense if
`U ×_S Spec k(s)` is dense in `X ×_S Spec k(s)` for every `s ∈ S`. The module expresses
this with the Library's `FibreGenerizationDense p U` (module
`Langlands.AlgebraicGeometry.FibreGenericPoints`): every point `x` has a generization in
`U` lying in the same fibre of `p`. When the fibres of `p` are locally Noetherian, for
instance when `p` is locally of finite type over a discrete valuation ring or a field,
the two notions agree: a point of a locally Noetherian space lies in the closure of an
open set `U` exactly when an irreducible component through it meets `U`, that is, when
the generic point of that component, a generization of the point, lies in `U`.

## `leftTranslation` and `rightTranslation`

For `f : X ⟶ S`, an open subscheme `D` of `X ×_S X` and a morphism `m : D ⟶ X` over `S`
(`m ≫ f = D.ι ≫ pullback.fst f f ≫ f`):

- `leftTranslation f D m hm : D ⟶ X ×_S X` is `(x, y) ↦ (x, m(x, y))`, the map `Φ` of
  BLR 5.1/1;
- `rightTranslation f D m hm : D ⟶ X ×_S X` is `(x, y) ↦ (m(x, y), y)`, the map `Ψ`.

## `BirationalGroupLaw f`

BLR 5.1/1 (printed p. 112) defines an `S`-birational group law on a smooth separated
`S`-scheme `X` of finite type with nonempty fibres as an `S`-rational map
`m : X ×_S X ⇢ X` such that (a) the universal translations `Φ` and `Ψ` are
`S`-birational and (b) `m` is associative, `(x y) z = x (y z)` whenever both sides are
defined. BLR 2.5 defines `S`-rational maps as classes of morphisms on `S`-dense open
subschemes and calls a map `S`-birational when a representative is an isomorphism onto
an `S`-dense open subscheme; the remark after 5.1/1 notes that it suffices to ask `Φ`
and `Ψ` to be open immersions on an `S`-dense open subscheme.

The structure `BirationalGroupLaw f` records one representative of such a law:

- `domain`: an open subscheme of `X ×_S X`, `S`-dense (`domain_dense`);
- `mul : domain ⟶ X` over `S` (`mul_comp`);
- `leftTranslation` and `rightTranslation` of `mul` are open immersions whose images are
  `S`-dense in `X ×_S X` (`isOpenImmersion_leftTranslation`, `leftTranslation_dense`,
  `isOpenImmersion_rightTranslation`, `rightTranslation_dense`);
- `assoc`: for every scheme `T` and `T`-valued points `a = (x, y)`, `c = (y, z)`,
  `b = (x y, z)` and `d = (x, y z)` of `domain` (the hypotheses record exactly these
  coordinate equalities), `mul ∘ b = mul ∘ d`.

The hypotheses on `X` itself (smooth, separated, finite type, nonempty fibres) are not
part of the structure; statements using it impose them.

Every `S`-birational group law in the sense of BLR has such a representative: shrink a
representative of `m` to an `S`-dense open on which `Φ` and `Ψ` are open immersions;
their images are then `S`-dense (remark after BLR 5.1/1). Conversely, a structure as above
defines an `S`-birational group law. Associativity of the representative where both
products are defined is BLR's condition (b) restricted to the domain of the
representative; when `X` is smooth and separated over `S`, two morphisms from a reduced
scheme to `X` agreeing on a dense open subscheme agree, so the two formulations of (b)
are equivalent.

## `BirationalGroupLaw.Solution m`

BLR 5.1/2 (printed p. 113) defines a solution of `m` as a smooth separated `S`-group
scheme `X̄` of finite type with group law `m̄`, an `S`-dense open subscheme `X' ⊆ X`
and an open immersion `X' ↪ X̄` such that (a) the image of `X'` is `S`-dense in `X̄`
and (b) `m̄` restricts to `m` on `X'`.

The structure `Solution m` has fields:

- `group : Langlands.GroupScheme S`, a group object in schemes over `S`, with `smooth`,
  `isSeparated`, `locallyOfFiniteType` and `quasiCompact` for its structure morphism;
- `domain : X.Opens`, `S`-dense in `X` (`domain_dense`), the subscheme `X'`;
- `embedding : domain ⟶ group.X.left` over `S` (`embedding_comp`), an open immersion
  (`isOpenImmersion_embedding`) with `S`-dense image (`embedding_dense`);
- `mul_eq`: for every scheme `T`, every `T`-valued point `a` of the domain of `m` and
  `T`-valued points `x`, `y`, `z` of `domain` with `a = (x, y)` and `m(a) = z`, the image
  of `z` in the group is the product of the images of `x` and `y`. The product is
  `lift x' y' ≫ μ`, the group law of `Hom(T, X̄)` over `S`, where `x'` and `y'` are the
  images of `x` and `y` viewed as morphisms over `S` from `T` with structure map
  `x ≫ domain.ι ≫ f`.

Condition `mul_eq` is BLR's condition (b): the rational map `X' ×_S X' ⇢ X̄` given by
`m` followed by the embedding agrees with the group law on the points where `m` is
defined with value in `X'`.
