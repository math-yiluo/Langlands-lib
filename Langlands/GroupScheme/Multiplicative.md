# The multiplicative group scheme and its roots-of-unity kernels

Author: Worker 223.

This module constructs, over an arbitrary scheme `S`, the actual multiplicative
group scheme `Gm S : CommGroupScheme S` and the group schemes of roots of unity
`mu S n : CommGroupScheme S`. It proves that their points over every
`T : Over S` are the global units and the `n`-th roots of unity of `Γ(T, 𝒪_T)`.
It also specializes these identifications to affine test schemes, compares them
with the published `Langlands.TateTwist.Level`, and constructs the canonical
base-change isomorphisms. All declarations are in the namespace
`Langlands.GroupScheme`.

## Source

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Chapter III, Examples 2 and 3 on printed p. 32 (PDF p. 36):

- Example 2. "This group scheme, denoted Gm,S, represents the functor which
  associates to an S-scheme T the multiplicative group Γ(T, O_T)^* of
  invertible elements of Γ(T, O_T). As a scheme, Gm = Spec(O_S[x, x^{-1}])."
  The multiplication is given by `x ↦ x ⊗ x`.
- Example 3. "Given a positive integer n, we have an S-group scheme µ_{n,S}
  which associates to an S-scheme T the subgroup of Gm(T) of elements whose
  order divides n." It is a closed subgroup scheme of Gm,S.
- The paragraph after Example 5 says that Examples 1–3 are defined over
  Spec(ℤ): `G_S = G_ℤ ×_{Spec ℤ} S`.

Section 3, (3.21)–(3.24), printed pp. 41–43 (PDF pp. 45–47), uses Gm as the
target of Cartier characters. That material is only motivation here: this
module proves no Cartier duality or representability.

The registered source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
kept at
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
PDF pp. 36 and 45–47 were read.

## The representing scheme

`Gm.laurentRing` is the Laurent polynomial ring `ℤ[t, t⁻¹]`, written as
`LaurentPolynomial (ULift ℤ)` so that it lives in the universe of `S`.
`Gm.coordUnit` is the coordinate `t`, as a unit.
`Gm.laurentHomEquiv A` is the universal property of this ring: ring maps
`ℤ[t, t⁻¹] → A` correspond to units of `A`, via the image of `t`. The inverse
map evaluates a Laurent polynomial at the given unit.

`Gm.specHomEquiv X R` identifies morphisms `X ⟶ Spec R` with ring maps
`R ⟶ Γ(X, ⊤)`, using Mathlib's `Scheme.toSpecΓ` and `Scheme.ΓSpecIso`.
Combining this with the previous step, `Gm.unitsHomEquiv X` identifies morphisms
`X ⟶ Spec ℤ[t, t⁻¹]` with `Γ(X, ⊤)ˣ`. The unit is the pullback of `t`.
`Gm.unitsHomEquiv_comp` states that precomposing with a morphism `g` applies
`Units.map` of `g.appTop`.

`Gm.toSpecZ S` is the unique morphism `S ⟶ Spec ℤ`, and `Gm.overSpecZ` is
`Spec ℤ[t, t⁻¹]` as a scheme over `Spec ℤ`. `Gm.scheme S` is its actual base
change `(Over.pullback (toSpecZ S)).obj overSpecZ`, as in the source.
`Gm.schemeHomEquiv T` is the universal property of this pullback: `S`-morphisms
`T ⟶ Gm.scheme S` are morphisms `T.left ⟶ Spec ℤ[t, t⁻¹]`. `Gm.homEquiv T` is
the resulting bijection with `Γ(T.left, ⊤)ˣ`, and `Gm.homEquiv_comp` is its
naturality.

## The group scheme `Gm S`

`Gm.unitsFunctor S` is the presheaf of commutative groups
`T ↦ Γ(T.left, ⊤)ˣ` on `Over S`. Its restriction maps are `Units.map` of the
global-sections maps. `Gm.representableBy S` says `Gm.scheme S` represents its
underlying set-valued functor.

`Gm S` is `Gm.scheme S` with the commutative group-object structure that
Mathlib's `CommGrpObj.ofRepresentableBy` transports from this functor. Its
multiplication, unit and inverse are therefore the morphisms that represent
multiplication, one and inversion of global units. This is the functorial
form of the source's formulas `x ↦ x ⊗ x`, `x ↦ 1` and `x ↦ x⁻¹`; the module
states the multiplication on points (`Gm.pointsEquiv_μ` below) and states no
Hopf-algebra formula. Neither the scheme nor the group law is a parameter of
the construction.

- `Gm.pointsIso S` is the isomorphism of group-valued presheaves between the
  published points functor `GroupScheme.points (Gm S).toGrp` and the units
  presheaf. It is Mathlib's `yonedaGrpObjIsoOfRepresentableBy`.
- `Gm.pointsEquiv S T : (T ⟶ (Gm S).X) ≃* Γ(T.left, ⊤)ˣ` is its component at
  `T`. `Gm.pointsEquiv_apply` says that its underlying map is `Gm.homEquiv T`,
  and `Gm.pointsEquiv_val` says that the unit attached to a point is the
  pullback of `t`.
- `Gm.pointsEquiv_mul` says the group law on points is multiplication of
  units.
- `Gm.pointsEquiv_naturality` says that a map of test schemes `a : T' ⟶ T`
  acts on units by `Units.map a.left.appTop`.
- `Gm.pointsEquiv_μ` says the multiplication morphism, as a point of `Gm S`
  over `Gm S ⊗ Gm S`, is the product of the units of the two projections.

## Group-scheme morphisms from maps of points

The section `Yoneda` holds generic Yoneda tools for group objects
`G H : Grp (Over S)`. They are internal tools, not source definitions.

- `pointsNatTrans` turns a family of homomorphisms
  `(T ⟶ G.X) →* (T ⟶ H.X)` that is natural in `T` into a morphism of
  group-valued presheaves.
- `homOfPoints` is the group-scheme homomorphism inducing that family, the
  preimage under Mathlib's full faithfulness of `yonedaGrp`.
  `comp_homOfPoints` says that composing a point with it applies the family.
- `hom_ext_points` says homomorphisms that agree on all points are equal.
- `isoOfPoints` turns a natural family of multiplicative equivalences into an
  isomorphism of group schemes. `comp_isoOfPoints_hom` and
  `comp_isoOfPoints_inv` describe its two directions on points, and
  `isoOfPoints_symm_naturality` gives naturality of the inverse family.

## Roots of unity

`mu S n` is the published actual torsion kernel
`GroupScheme.torsion (Gm S).toGrp n`, the kernel of the `n`-th power
endomorphism, viewed as a commutative group scheme. `mu.toGrp_eq` records this
equality. `mu.incl S n : mu S n ⟶ Gm S` is the published kernel inclusion
`torsionι`, and `mu.groupHom_incl` records this.

The source takes `n` positive. Lean accepts every natural number `n`; for
`n = 0` the power map is trivial, so `mu S 0` is the kernel of the trivial
endomorphism, and `rootsOfUnity 0` is the whole unit group. The statements
below hold for every `n`. No étaleness of `mu S n` is asserted for any `n`.

- `mu.torsionPointsUnitsEquiv S n T` restricts `Gm.pointsEquiv S T` to an
  equivalence between the published `torsionPoints` subgroup and
  `rootsOfUnity n Γ(T.left, ⊤)`. A multiplicative equivalence preserves powers
  and one, so `x ^ n = 1` exactly when its unit is an `n`-th root of unity.
- `mu.pointsEquiv S n T : (T ⟶ (mu S n).X) ≃* rootsOfUnity n Γ(T.left, ⊤)`
  composes the published `torsionPointsEquiv` with the previous equivalence.
- `mu.pointsEquiv_val` says that the unit underlying the root of unity of `x`
  is the `Gm`-unit of `x ≫ ι`. Thus the inclusion `mu S n ⟶ Gm S` becomes the
  inclusion of roots of unity into units. `mu.pointsEquiv_symm_comp_ι` is the
  inverse form.
- `mu.pointsEquiv_naturality` says a map of test schemes acts by
  `restrictRootsOfUnity` of its global-sections map.

## Affine test schemes

For a ring map `φ : R ⟶ R'` and `f : Spec R ⟶ S`, `Gm.affineMap φ f` is the
`S`-morphism `Spec R' ⟶ Spec R` given by `Spec.map φ`.

- `Gm.affinePointsEquiv f : (Over.mk f ⟶ (Gm S).X) ≃* Rˣ` composes
  `Gm.pointsEquiv` with the units of `Scheme.ΓSpecIso R : Γ(Spec R, ⊤) ≅ R`.
  `Gm.affinePointsEquiv_val` is this formula.
- `Gm.affinePointsEquiv_naturality` says that precomposition with
  `Gm.affineMap φ f` corresponds to `Units.map φ`. It follows from
  `Gm.pointsEquiv_naturality` and Mathlib's `Scheme.ΓSpecIso_naturality`.
- `mu.affinePointsEquiv n f : (Over.mk f ⟶ (mu S n).X) ≃* rootsOfUnity n R`
  is `mu.pointsEquiv` followed by `MulEquiv.restrictRootsOfUnity` of the same
  ring isomorphism. `mu.affinePointsEquiv_val` says its underlying unit is
  `Gm.affinePointsEquiv f (x ≫ ι)`.
- `mu.affinePointsEquiv_naturality` says that precomposition with
  `Gm.affineMap φ f` corresponds to `restrictRootsOfUnity φ n`.

## Comparison with `TateTwist.Level`

The published `Langlands.TateTwist.Level A n` is `Additive (rootsOfUnity n A)`.
It comes with `toUnit`, the inclusion into `Additive Aˣ`, and transition maps
`TateTwist.transition A h` for `h : n ∣ m`, given by `ζ ↦ ζ ^ (m / n)`. This
module does not redefine that twist, and no primitive root is chosen.

- `mu.pointsLevelEquiv n T : Additive (T ⟶ (mu S n).X) ≃+ TateTwist.Level Γ(T.left, ⊤) n`
  and `mu.levelEquiv n f : Additive (Over.mk f ⟶ (mu S n).X) ≃+ TateTwist.Level R n`
  are the additive forms of `mu.pointsEquiv` and `mu.affinePointsEquiv`.
  `mu.toUnit_pointsLevelEquiv` and `mu.toUnit_levelEquiv` say that `toUnit`
  of the image of `x` is the `Gm`-unit of `x ≫ ι`.
- `rootsTransition A h : rootsOfUnity m A →* rootsOfUnity n A` is the
  multiplicative form of `TateTwist.transition A h`
  (`toAdditive_rootsTransition`). `rootsTransition_val` says it is
  `ζ ↦ ζ ^ (m / n)`. `rootsTransition_restrict` says it commutes with
  `restrictRootsOfUnity` of any ring map.
- `mu.transition S h : mu S m ⟶ mu S n` is the group-scheme homomorphism
  built by `homOfPoints` from `rootsTransition`. Its naturality on points is
  `mu.transition_naturality`. `mu.pointsEquiv_transition` says it acts on
  points by `ζ ↦ ζ ^ (m / n)`. `mu.pointsLevelEquiv_transition` and
  `mu.levelEquiv_transition` say it corresponds to `TateTwist.transition`
  under the two level identifications.
- `mu.transition_incl` says that `mu.transition S h` followed by the inclusion
  equals the inclusion followed by the published endomorphism
  `multiplication (Gm S).toGrp (m / n)`.

## Base change

Fix a morphism of schemes `b : S' ⟶ S`. The published functor
`(Over.pullback b).mapGrp` is the actual base change of group schemes, and
`baseChangePointsEquiv` is the multiplicative pullback adjunction on points.

- `Gm.baseChangeUnitsEquiv b T` identifies the points of the base change of
  `Gm S` over `T : Over S'` with `Γ(T.left, ⊤)ˣ`. It is
  `baseChangePointsEquiv` followed by `Gm.pointsEquiv S` over the composite
  `T → S' → S`, as `Gm.baseChangeUnitsEquiv_apply` records.
  `Gm.baseChangeUnitsEquiv_naturality` is its naturality.
- `Gm.baseChangeIso b : (Over.pullback b).mapGrp.obj (Gm S).toGrp ≅ (Gm S').toGrp`
  is the canonical isomorphism, obtained by `isoOfPoints` from the natural
  family `baseChangeUnitsEquiv` followed by the inverse of
  `Gm.pointsEquiv S'` (naturality: `Gm.baseChangeIso_naturality`). Both sides
  represent the global units, so this is the source's `G_S' = G_S ×_S S'` for
  `Gm`. `Gm.pointsEquiv_baseChangeIso_hom` and
  `Gm.baseChangeUnitsEquiv_baseChangeIso_inv` say both directions preserve the
  underlying unit.
- `Gm.commBaseChangeIso b : (CommGroupScheme.baseChange b).obj (Gm S) ≅ Gm S'`
  is the same isomorphism in `CommGroupScheme S'`.
  `Gm.groupHom_commBaseChangeIso_hom` and `Gm.groupHom_commBaseChangeIso_inv`
  record its underlying group-object morphisms.
- `mu.baseChangeRootsEquiv b n T`, its `_apply` and `_naturality` lemmas, and
  `mu.baseChangeIso b n`, `mu.pointsEquiv_baseChangeIso_hom`,
  `mu.baseChangeRootsEquiv_baseChangeIso_inv` and `mu.commBaseChangeIso b n`
  are the same constructions for `mu`, with roots of unity in place of units.
  `mu.groupHom_commBaseChangeIso_hom` records the underlying morphism.
- `mu.baseChangeRootsEquiv_val` says the unit underlying a base-changed point
  of `mu S n` is the `Gm.baseChangeUnitsEquiv` value of its composite with the
  base change of the inclusion. It uses the published
  `baseChangePointsEquiv_comp`.
- `mu.baseChangeIso_hom_ι` and its commutative form
  `mu.commBaseChangeIso_hom_incl` say that the base-change isomorphisms of `mu`
  and `Gm` commute with the inclusions. The proof checks this on points with
  `hom_ext_points`.

The base-change isomorphism for `mu` is built directly from points; the
published `torsionBaseChangeIso` is not used, and no comparison with it is
stated.

## Scope

This module proves no Cartier representability, no duality of isogeny kernels,
no Weil pairing, and no finiteness, flatness, étaleness or rank result for
`mu S n`. Its only inputs are `S`, test schemes over `S`, natural numbers, ring
maps and morphisms of schemes. There are no hypothesis fields.
