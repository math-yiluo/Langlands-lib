# Actual parabolics in a represented dynamic Levi

Author: Worker 1291.

`DynamicLeviParabolicCorrespondenceStatement` is a proposition target, not a
proof. Let `k : Type u` be any field, let `G` be connected reductive over `k`,
and let `χ : Gm → G` be any actual cocharacter. For every closed group-scheme
embedding `j : L → G` representing the actual functor `Dynamic.centralizer χ`,
the target asserts an order isomorphism

`ParabolicFunctor L ≃o ParabolicFunctorBelow (Dynamic.parabolic χ)`.

Both sides consist of actual subgroup functors on all schemes over `Spec k`.
`IsParabolicFunctor`, reused by the subtype definitions, means the all-test
range of an actual representative satisfying the existing
`IsParabolicSubgroup`. Its equivalence with parabolicity of any closed
representative is proved in `Rational.ParabolicFunctor`. The order is
inclusion on every test scheme; an order isomorphism is in particular a
bijection preserving and reflecting that inclusion.

The target specifies both maps as equalities of subgroup functors:

- The forward map sends `F` to `Dynamic.extendFromCentralizer χ j hj F`.
  By `Dynamic.mem_extendFromCentralizer`, its points on every original test
  scheme `T` are exactly `(l ≫ j) * n`, where `l ∈ F(T)` and
  `n ∈ Dynamic.unipotent χ(T)`. This is the two-factor product itself.
- The inverse map sends `Q` to `Q.comap j`. Its points are exactly those
  `l : T → L` for which `l ≫ j ∈ Q(T)`. Mapping back into `G` gives
  `range j ⊓ Q`, by the existing `SubgroupFunctor.map_comap` theorem.

These functor equalities include nonreduced and non-affine test schemes.
At the identity test `Over.mk (𝟙 (Spec k))`, they give the identical formulas
for the actual rational-point groups. The published
`mem_extendFromCentralizer_rationalPointSubgroup`,
`mem_comap_rationalPointSubgroup`, and
`map_comap_rationalPointSubgroup` interfaces spell out those comparisons.
The represented-point equivalence `hj.rationalPointsEquiv` identifies
`L(k)` with the actual identity-test subgroup `Z_G(χ)(k)`. No topology or
quotient of rational-point groups enters the statement.

The assumptions are only connected reductivity of `G`, the cocharacter, and
the closed representative of its centralizer. In particular, reductivity of
`L`, parabolicity of the extension and inverse image, the inverse laws, and
the structural correspondence are not premises. Reductivity of arbitrary
represented dynamic centralizers retains its separate statement and proof
owner. No splitness, characteristic restriction, root-classification
hypothesis, or general-linear model is imposed.

The classical source is Renard, *Représentations des groupes réductifs
p-adiques*, edition dated 9 July 2026, V.3.8 on printed p.111/PDF p.117 and
V.3.11 on printed p.112/PDF p.118. Renard fixes a maximal split torus and
states the correspondence for standard, respectively semistandard,
parabolics with the chosen compatible Levi factors. The present target is
the underlying full algebraic correspondence, so it deliberately ranges
over all rational parabolics in the represented Levi and all ambient
parabolics contained in `P_G(χ)`.

Borel–Tits, *Groupes réductifs* (1965), Proposition 4.4(c), printed
pp.86–87/PDF pp.33–34, states that parabolics contained in a parabolic are
the semidirect products of parabolics in a Levi with the unipotent radical.
Sections 4.6–4.8, printed pp.87–88/PDF pp.34–35, supply the rational
parabolic and Levi setting. Milne, *Algebraic Groups* (2017), §25.1 and
§25.6–25.7, printed pp.544–546/PDF pp.560–562, supplies the cocharacter
realization of rational parabolics and their dynamic unipotent factors.
The official errata, snapshot 2026-11-02, restricts §25.6(b) to a minimal
parabolic; no identification of an arbitrary Levi with the centralizer of
a maximal split torus is used here. The errata's printed-p.549 warning
about the classical relative-root-system proof also supplies no hypothesis.

The provenance is derived: actual `Grp (Over (Spec k))` representatives,
all-test product formulas, arbitrary-universe quantification, and the
specified order isomorphism are the Library's explicit algebraic
formulation of these sources. Establishing this proposition, including its
unrestricted test-scheme meaning, remains a separate proof obligation.
