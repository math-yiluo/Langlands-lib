# Parabolic subgroups, unipotent radicals and Levi subgroups over a base scheme

Author: Worker 75.

This module supplies three predicates on homomorphisms of group schemes over
an arbitrary base scheme `S`. They are the relative counterparts of the existing
ground-field predicates `IsParabolicSubgroup`, `IsUnipotentRadical` and
`IsRationalLeviSubgroup`. The module only defines these predicates. It does not
construct a unipotent radical or a Levi subgroup, and it asserts no existence,
uniqueness, closedness or conjugacy theorem.

## Fibre homomorphisms

For a homomorphism `f : H ⟶ G` of group schemes over `S` and a point `s` of `S`:

- `RelativeLevi.residueFiberHom f s` is the base change of `f` along
  `Spec κ(s) ⟶ S` (Mathlib's `S.fromSpecResidueField s`), where `κ(s)` is the
  residue field at `s`. It is written over `Spec (CommRingCat.of κ(s))` so that
  the ground-field predicates over a field type apply to it.
- `RelativeLevi.geometricFiberHom f s` is the base change of `f` along the
  existing `geometricPoint S s : Spec κ(s)^alg ⟶ S`, where `κ(s)^alg` is
  Mathlib's algebraic closure of `κ(s)`. Its source and target are the
  existing `geometricFiber H s` and `geometricFiber G s`.

Both are abbreviations of `(GroupScheme.baseChange _).map f`.

## Parabolic subgroups

`IsRelativeParabolicSubgroup i`, for `i : P ⟶ G`, has four fields:

- `P` is smooth over `S` (`Smooth P.X.hom`);
- `P` is affine over `S` (`IsAffineHom P.X.hom`);
- `i` is a monomorphism of `S`-schemes (`Mono i.hom.hom`, the same monomorphism
  condition as in `SubgroupFunctor.IsRepresentedBy`). By Mathlib's
  `Over.mono_of_mono_left` and `Over.mono_left_of_mono`, this is equivalent to
  the underlying morphism of schemes being a monomorphism;
- for every point `s` of `S`, the residue fibre `i_s : P_s ⟶ G_s` over `κ(s)`
  satisfies `IsParabolicSubgroup`.

The predicate does not require `i` to be a closed immersion. The source proves
closedness as Proposition 5.2.3. The field predicate `IsParabolicSubgroup`
requires its fibre map to be a closed subgroup. This adds nothing to the source
definition, because a monomorphism of group schemes of finite type over a field
is a closed immersion. The predicate places no condition on `G`. The source
defines parabolic subgroups only of reductive group schemes, so statements about
them should assume `IsReductive G` separately.

## Unipotent radicals

`IsRelativeUnipotentRadical r`, for `r : U ⟶ P`, has four fields:

- `r` is a closed subgroup (`IsClosedSubgroup r`, a closed immersion of
  underlying schemes);
- `U` is smooth over `S`;
- the image of `r` is normal in `P` on every test scheme
  (`(SubgroupFunctor.range r).IsNormal`);
- for every point `s` of `S`, the geometric fibre `r_{s̄} : U_{s̄} ⟶ P_{s̄}`
  satisfies `IsUnipotentRadical`. Over the algebraically closed field `κ(s)^alg`,
  this predicate says that `U_{s̄}` is a smooth connected unipotent normal closed
  subgroup of `P_{s̄}` whose image contains that of every such subgroup, that is,
  that `r_{s̄}` represents the unipotent radical `R_u(P_{s̄})`.

This is the defining property of `R_u(P)` in Corollary 5.2.5 of the source. For
a parabolic subgroup `P` of a reductive group scheme, that corollary proves that
such an `R_u(P)` exists and is unique. Neither fact is part of this module.

## Levi subgroups

`IsRelativeLeviSubgroup l`, for `l : L ⟶ P`, has three fields:

- `l` is a closed subgroup;
- `L` is smooth over `S`;
- there exist a group scheme `U` over `S` and `r : U ⟶ P` with
  `IsRelativeUnipotentRadical r` such that the existing
  `subgroupMultiplication l r : L ×_S U ⟶ P`, `(x, u) ↦ l(x) r(u)`, is an
  isomorphism of `S`-schemes.

The source asks that `L ⋉ R_u(P) → P` be an isomorphism. The underlying morphism
of schemes of this semidirect-product homomorphism is the multiplication map
`(x, u) ↦ x u`, and a homomorphism of group schemes is an isomorphism exactly
when its underlying morphism of schemes is. The isomorphism is required of the
actual morphism of schemes over `S`, not only on points over fields.

The source fixes `R_u(P)` as the unique subgroup of Corollary 5.2.5, while the
predicate asks for some `r` with `IsRelativeUnipotentRadical r`. For a parabolic
subgroup of a reductive group scheme the two agree, by the uniqueness half of
Corollary 5.2.5: any two such `r` have equal images, so their sources are
isomorphic over `P` and the two multiplication maps differ by an isomorphism.
That uniqueness is a theorem of the source, not proved here. Like the source
definition, the predicate does not require `L` to be reductive.

The source also introduces the functor `Lev(P)`, whose value on an `S`-scheme
`S'` is the set of Levi `S'`-subgroups of `P_{S'}`. That functor is not formalized
here. Its values are the images of the homomorphisms satisfying
`IsRelativeLeviSubgroup` after base change to `S'`.

## Source

Brian Conrad, *Reductive group schemes* (SGA3 summer school notes, 2014),
registered as `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`. Printed and
PDF page numbers agree.

- Definition 5.2.1, p.151: a parabolic subgroup of a reductive group scheme
  `G → S` is a smooth `S`-affine `S`-group `P` with a monic homomorphism
  `P → G` such that `P_s` is parabolic in `G_s` for all `s ∈ S`. The text
  following it says that closedness is not required.
- Proposition 5.2.3, p.152: such a `P → G` is a closed immersion.
- Corollary 5.2.5, p.153: the unique smooth closed normal `S`-subgroup
  `R_u(P) ⊂ P` whose geometric fibre `R_u(P)_{s̄}` is the unipotent radical of
  `P_{s̄}` for all `s ∈ S`.
- Definition 5.4.2, p.174: a Levi subgroup of `P` is a smooth closed `S`-subgroup
  `L ⊂ P` such that `L ⋉ R_u(P) → P` is an isomorphism, together with the
  functor `Lev(P)`.

The field predicates used on the fibres are the existing Library declarations
`IsParabolicSubgroup` (in `Langlands.GroupScheme.Absolute.Borel`) and
`IsUnipotentRadical` (in `Langlands.GroupScheme.Reductive.UnipotentRadical`).
