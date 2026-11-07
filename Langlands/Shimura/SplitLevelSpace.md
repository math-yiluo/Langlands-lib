# Level spaces at split levels

Author: Worker 13.

This internal construction describes the level spaces of a group that splits
as a product, at levels whose first component is fixed. Let `Γ` be a group
acting on a space `X`, let `ι : Γ →* G`, and let `e : G ≃ₜ* H × H'` be an
isomorphism of topological groups. Write `e (ι γ) = (ι₁ γ, ι₂ γ)` for
homomorphisms `ι₁ : Γ →* H` and `ι₂ : Γ →* H'`. For a compact open level `K₀`
of `H`, the module identifies the level space of `G` at `e⁻¹ (K₀ × K')`,

`Γ \ (X × G) / e⁻¹ (K₀ × K')`,

with the level space of `H'` at `K'` for the domain `X × H ⧸ K₀`,

`Γ \ ((X × H ⧸ K₀) × H') / K'`.

Here `Γ` acts on `H ⧸ K₀` by left multiplication through `ι₁`. The module
proves this homeomorphism, shows that it is compatible with the right
translations by `H'`, and assembles it into an isomorphism of level towers
over the levels of `H'`. For a presheaf on spaces, it then gives the induced
isomorphisms of towers, of colimits with their action of `H'`, and of smooth
representations.

## Motivation and scope

Proposition 4.10 on printed p. 311 of Harris (1999), *Galois properties of
cohomological automorphic forms on GL(n)*
(`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`), lets the
level `K(N)^{ℓ,p}` away from `ℓ` and `p` vary, with
`GG(A_f^{ℓ,p})`-equivariance. The published
`Langlands.Shimura.SplitLevelTower` forms the away tower
`K' ↦ F (e⁻¹ (K₀ × K'))` of a presheaf `F` on the levels of `G` for a splitting
`e`, with its action of `H'`. This module computes that tower when `F` is a
presheaf on level spaces: the away tower is again a tower of level spaces, now
of `H'`, for a larger domain. Harris's passage is motivation only; no
statement from it is formalized. The identification itself, the domain
`X × H ⧸ K₀` and the hypothesis on `ι₁` and `ι₂` are implementation choices,
not attributed to a source.

The module constructs no splitting of a particular group, no Shimura variety
and no cohomology. It does not treat levels of `G` that are not of the form
`e⁻¹ (K₀ × K')`, and it does not vary `K₀`.

## Inputs

All declarations are in namespace `Langlands.Shimura.LevelSpace`.

The published `Langlands.Shimura.Levels` provides the transporter category
`CompactOpenLevel G` of compact open subgroups of a topological group `G`,
with `K.subgroup` the underlying subgroup and arrows `a : K ⟶ L` carrying
elements `a.element` with `a.respects`. For `Γ` acting on `X` and
`ι : Γ →* G`, it provides the relation `levelSetoid ι K` on `X × G`, under which
`(x, g)` is related to `(γ • x, ι γ * g * k)` for `γ : Γ` and `k ∈ K`; the
quotient `LevelSpace ι K` with classes `mk K x`, `mk_eq_mk`, quotient
topology and `continuous_mk`; the right translation `translate g hg`, which
sends the class of `(x, g')` to the class of `(x, g' * g)`; and the tower
`tower : CompactOpenLevel G ⥤ TopCat` of level spaces with transitions
`translate a.element a.respects`.

The published `Langlands.Shimura.PEL.TraceSimilitudesLevels` provides the
transported level `CompactOpenLevel.transport`. The published
`Langlands.Shimura.PartialLevelTower` provides the product level
`CompactOpenLevel.prod K₀ K'`. The published
`Langlands.Shimura.SplitLevelTower` provides `mem_transport_symm_prod` (`g` lies
in `transport e.symm (prod K₀ K')` exactly when `(e g).1 ∈ K₀` and
`(e g).2 ∈ K'`), the level functor `awayOver e K₀` over `awayHom e`, whose
functor sends `K'` to `transport e.symm (prod K₀ K')` and whose arrows have
elements `e.symm (1, a.element)`, the away tower `LevelColimit.awayTower e K₀ F`
and the smooth representation `LevelColimit.awaySmoothRep e K₀ F hF`.

The published `Langlands.Shimura.LevelColimit` provides the ordered synonym
`Ordered G`, the object `LevelColimit.action F` of `Action C G` on the colimit
of a presheaf `F` on levels, the functor `LevelColimit.functor G C` sending
`F` to `action F`, the smooth representation `LevelColimit.smoothRep F hF`, and
`isLevelTrivial_tower ι P`: a presheaf `P` on spaces restricted along `tower`
is level-trivial.

Mathlib provides `QuotientGroup` cosets with
`QuotientGroup.isOpenQuotientMap_mk`, `IsOpenQuotientMap`, `TopCat.isoOfHomeo`,
`NatIso.ofComponents`, `Functor.isoWhiskerRight`, `Rep.ActionToRep` and
`ObjectProperty.isoMk`.

## The domain

Let `Γ` and `H` be groups, `Γ` acting on `X`, and `ι₁ : Γ →* H`.

- `AwayDomain X ι₁ K₀` is `X × (H ⧸ K₀)` for a subgroup `K₀` of `H`. Its
  instance `MulAction Γ` is the diagonal action, given on `X` by the action of
  `Γ` and on `H ⧸ K₀` by left multiplication through `ι₁`. When `X` and `H`
  have topologies it carries the product topology of `X` and the quotient
  topology of `H ⧸ K₀`.
- `AwayDomain.mk ι₁ K₀ x c` is the point `(x, c)`, and
  `AwayDomain.smul_mk ι₁ K₀ γ x h` states, by `rfl`, that `γ` sends
  `(x, h K₀)` to `(γ • x, ι₁ γ * h K₀)`.

## The two components

For `ι : Γ →* G` and `e : G ≃ₜ* H × H'`:

- `factorRestriction ι e : Γ →* H` and `awayRestriction ι e : Γ →* H'` are the
  first and second components of `e ∘ ι`.
- `apply_eq_factorRestriction_awayRestriction ι e γ`: `e (ι γ)` is
  `(factorRestriction ι e γ, awayRestriction ι e γ)`, by `rfl`.

The declarations below take any `ι₁ : Γ →* H`, `ι₂ : Γ →* H'` and a hypothesis
`hι : ∀ γ, e (ι γ) = (ι₁ γ, ι₂ γ)`, so that they apply to homomorphisms that
agree with these components without being definitionally equal to them.

## The identification at one level

Let `K₀` be a compact open level of `H` and `K'` one of `H'`.

- `awayPoint e ι₁ K₀ (x, g)` is the point `((x, (e g).1 K₀), (e g).2)` of
  `AwayDomain X ι₁ K₀ × H'`.
- `awayInvFun ι e ι₁ K₀ K'` sends `((x, h K₀), h')` to the class of
  `(x, e.symm (h, h'))` in the level space of `G` at
  `transport e.symm (prod K₀ K')`. It does not depend on the representative
  `h`: changing `h` to `h k` with `k ∈ K₀` multiplies `e.symm (h, h')` on the
  right by `e.symm (k, 1)`, which lies in that level. `awayInvFun_mk` records
  the value on `((x, h K₀), h')`, by `rfl`.
- `awayPoint_respects hι K₀ K' x y`: if `x` and `y` are related by
  `levelSetoid ι (transport e.symm (prod K₀ K'))`, then their points are related
  by `levelSetoid ι₂ K'`. `awayInvFun_respects hι K₀ K' p q`: related points of
  `AwayDomain X ι₁ K₀ × H'` have the same image under `awayInvFun`.
- `awayEquiv X hι K₀ K'` is the resulting equivalence

  `LevelSpace ι (transport e.symm (prod K₀ K')) ≃ LevelSpace ι₂ K'`,

  the second level space taken for the domain `AwayDomain X ι₁ K₀`. Its
  forward map is induced by `awayPoint` and its inverse by `awayInvFun`.
  `awayEquiv_mk` and `awayEquiv_symm_mk` record the values on classes, by
  `rfl`.
- `awayEquiv_translate hι K₀ h' hg hh q`: for levels `K'` and `L'` of `H'`,
  `h' : H'` conjugating `K'` into `L'` (hypothesis `hh`) and the corresponding
  hypothesis `hg` for `e.symm (1, h')`, applying `awayEquiv` at `L'` after right
  translation by `e.symm (1, h')` equals applying `awayEquiv` at `K'` and then
  right translation by `h'`.

Assume moreover that `X` has a topology and `H` is a topological group.

- `continuous_awayPoint e ι₁ K₀`: `awayPoint` is continuous.
- `isOpenQuotientMap_awayProjection ι₁ K₀`: the projection
  `((x, h), h') ↦ ((x, h K₀), h')` from `(X × H) × H'` is an open quotient map.
- `continuous_awayInvFun ι e ι₁ K₀ K'`: `awayInvFun` is continuous. Its
  composite with the projection is the continuous map
  `((x, h), h') ↦ mk (x, e.symm (h, h'))`.
- `awayHomeomorph X hι K₀ K'` is `awayEquiv X hι K₀ K'` as a homeomorphism
  of level spaces, with `awayHomeomorph_apply` (by `rfl`).

## The towers

Assume now that `G`, `H` and `H'` lie in one universe and are topological
groups, and that `X` has a topology.

- `awayTowerIso X hι K₀` is the natural isomorphism

  `(awayOver e K₀).functor ⋙ tower (X := X) (ι := ι) ≅ tower (X := AwayDomain X ι₁ K₀) (ι := ι₂)`

  of functors from `CompactOpenLevel H'` to `TopCat`. Its component at `K'` is
  `awayHomeomorph X hι K₀ K'`, and naturality is `awayEquiv_translate`.
  `awayTowerIso_hom_app_apply` records that the component sends `q` to
  `awayEquiv X hι K₀ K' q`, by `rfl`.

Let `P : TopCatᵒᵖ ⥤ C` be a presheaf on spaces with values in a category `C`.

- `awayTowerPresheafIso X hι K₀ P` is the isomorphism

  `LevelColimit.awayTower e K₀ ((tower (X := X) (ι := ι)).op ⋙ P) ≅ (tower (X := AwayDomain X ι₁ K₀) (ι := ι₂)).op ⋙ P`

  of presheaves on the levels of `H'`, obtained by whiskering the opposite of
  the inverse of `awayTowerIso` with `P`. `awayTowerPresheafIso_hom_app`
  records its component at `K'` as `P.map ((awayTowerIso X hι K₀).inv.app K').op`,
  by `rfl`.
- `awayActionIso X hι K₀ P`: if colimits of shape `(Ordered H')ᵒᵖ` exist in `C`,
  the image of `awayTowerPresheafIso` under `LevelColimit.functor H' C`, an
  isomorphism of the objects `LevelColimit.action` of `Action C H'` on the two
  colimits.
- `awaySmoothRepIso X hι K₀ P`: for a commutative ring `R`, a presheaf `P` of
  `R`-modules, and colimits of shapes `(Ordered G)ᵒᵖ` and `(Ordered H')ᵒᵖ` in
  `ModuleCat R`, an isomorphism of smooth representations of `H'`

  `LevelColimit.awaySmoothRep e K₀ ((tower (X := X) (ι := ι)).op ⋙ P) _ ≅ LevelColimit.smoothRep ((tower (X := AwayDomain X ι₁ K₀) (ι := ι₂)).op ⋙ P) _`.

  It is `ObjectProperty.isoMk` applied to the image of `awayActionIso` under
  `Rep.ActionToRep R H'`. The level-triviality arguments are
  `isLevelTrivial_tower ι P` and `isLevelTrivial_tower ι₂ P`.

## Proof outline

`awayPoint_respects` takes a relation `(y.1, y.2) = (γ • x.1, ι γ * x.2 * k)`
with `(e k).1 ∈ K₀` and `(e k).2 ∈ K'`, applies `e` and `hι` to get the two
components `(e y.2).1 = ι₁ γ * (e x.2).1 * (e k).1` and
`(e y.2).2 = ι₂ γ * (e x.2).2 * (e k).2`, and absorbs `(e k).1` into the coset
`K₀`. `awayInvFun_respects` reverses this: a relation
`((y, d), j') = ((γ • x, ι₁ γ * a K₀), ι₂ γ * h' * k')` is witnessed in `G` by
`γ` and `e.symm (1, k')`, checked after applying `e`. The two composites of
`awayEquiv` are the identity because `e.symm` and `e` are inverse.
`awayEquiv_translate` is a computation on representatives. Continuity of the
forward map uses `continuous_awayPoint` and `Continuous.quotient_map'`, and of
the inverse `isOpenQuotientMap_awayProjection` and the universal property of
the quotient topology. The tower isomorphism is `NatIso.ofComponents` of
`TopCat.isoOfHomeo`. The presheaf, action and smooth-representation
isomorphisms are images of the tower isomorphism under whiskering,
`LevelColimit.functor H' C` and `Rep.ActionToRep R H'`.
