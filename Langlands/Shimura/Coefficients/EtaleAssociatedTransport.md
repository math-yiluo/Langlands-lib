# Transport of associated coefficient sheaves along etale morphisms

This file constructs maps between associated (invariant) coefficient sheaves
that change the base scheme, the cover, the deck group and the coefficient
module at the same time, and proves their identity, composition, refinement
and scaling laws. It is an internal construction. It is built only from the
Library's associated-sheaf comparisons:
[EtaleConstantAssociatedPullback](EtaleConstantAssociatedPullback.md),
[EtaleConstantAssociatedPullbackCoherence](EtaleConstantAssociatedPullbackCoherence.md),
[EtaleCrossCover](EtaleCrossCover.md),
[EtaleCrossCoverPullback](EtaleCrossCoverPullback.md),
[CrossCover](CrossCover.md), the invariant inclusion of
[VaryingCoverInverse](VaryingCoverInverse.md), and the cover comparison
theorem `etaleAssociatedCoverComparison` of
[EtaleCoverComparisonProof](EtaleCoverComparisonProof.md). No theorem from the
literature is assumed or transcribed.

The construction serves the level-change maps of Harris's coefficient systems.
For an inclusion or translation of levels `V → U` and torsion stages `k, k'`,
the sheaf at `(U, k)` is associated with the cover `S_{U_k} → S_U` and a
finite lattice quotient. The sheaf at `(V, k')` is associated with a different
cover `S_{V_{k'}} → S_V` and another quotient. The two covers become
comparable only on a common refinement `S_T → S_V`. A transport datum records
exactly this common refinement and the maps out of it.

## Objects, universes and hypotheses

All schemes, the commutative ring `R`, module carriers and deck groups use
universe `u`. Write `constant Z` for the constant-sheaf functor
`constantSheaf (Scheme.smallEtaleTopology Z) (ModuleCat R)`; this local notation
is used throughout the Lean file. For a cover `Y : Action X.Etale G` and a
representation `M : Action (ModuleCat R) G`, write `L_X(Y, M)` for the
associated sheaf `(etaleAssociatedFunctor X Y).obj M`. Write `ι_Y(M)` for its
invariant inclusion `etaleAssociatedInclusion X Y M` into the product sheaf
`U ↦ M(Y × U)` (the sheaf `(productSheaf _ Y.V).obj ((constant X).obj M.V)`).
Write `cP(a)` for `coverPullback _ a _`, the restriction of sections of product
sheaves along a morphism `a` of cover objects. Write `r_f` for the small-etale
restriction `EtalePullback.restriction f (ModuleCat R)`, and `f^* Y` for the
base change `(etaleTorsorPullbackFunctor f G).obj Y`. Write
`λ_f(Y, M) : r_f L_X(Y, M) ⟶ L_Z(f^* Y, M)` for the hom component of
`etaleConstantAssociatedPullback f R Y` at `M`.

## Cross-cover maps on sections over the cover

For `φ : H →* G` and an equivariant cover map `a : Y' ⟶ Y|_H`, write
`K(a, c)` for `etaleCrossCoverMap X φ a c`, where `c : M|_H ⟶ N`.
`etaleCrossCoverMap_inclusion` restates the Library's `crossCoverMap_inclusion`
with the underlying cover and coefficient morphisms supplied separately, as
`a₀ : Y'.V ⟶ Y.V` and `c₀ : M.V ⟶ N.V` with `a.hom = a₀` and `c.hom = c₀`:

```text
K(a, c) ≫ ι_Y'(N) = ι_Y(M) ≫ cP(a₀) ≫ productSheaf(Y'.V).map((constant X).map c₀).
```

Stating the equation with `a₀` and `c₀` gives its source and target the
unrestricted objects `Y.V`, `Y'.V`, `M.V` and `N.V`, rather than their
`Action.res` presentations. These agree only up to unfolding, and the unfolded
forms are what later rewriting needs. `etaleCrossCoverMap_id_inclusion` is the
case `c = 𝟙`, where the coefficient factor disappears.
`etaleCrossCoverMap_id_inclusion_self` is its same-group form with
`φ = MonoidHom.id G` and the identity of `M`. This is the form in which
`etaleConstantAssociatedPullback_id` and
`etaleConstantAssociatedPullback_comp` state their correction maps.

The imported instance `productSheaf_additive` from `AssociatedComplex` proves that
`productSheaf J Y` is an
additive functor for every site `J` with binary products and every object
`Y`. The components of a sum of sheaf morphisms are sums of components, and
the components of `productSheaf J Y` on a morphism are components of that
morphism, so `map_add` holds componentwise by definition.

## Base change of cover maps

The following definitions only fix the types of existing morphisms:

* `etaleCoverMapPullback g a` is `(etaleObjectPullback g).map a` for
  `a : A.V ⟶ B.V`. It has type `(g^* A).V ⟶ (g^* B).V`.
* `etaleTorsorPullbackCompMap f g Y` is the underlying morphism of
  `(etaleTorsorPullbackComp f G g).hom.app Y`. It has type
  `((g ≫ f)^* Y).V ⟶ (g^* (f^* Y)).V`.
* `etaleTorsorPullbackIdMap X Y` is the underlying morphism of
  `(etaleTorsorPullbackId X G).hom.app Y`. It has type `((𝟙 X)^* Y).V ⟶ Y.V`.

## Transport data

`EtaleTransportDatum f Y Y' M M'` is defined for `f : Z ⟶ X`, covers
`Y : Action X.Etale G` and `Y' : Action Z.Etale H`, and representations `M` of
`G` and `M'` of `H`. Its fields are:

* a deck group `group` with homomorphisms `toSourceGroup : group →* G` and
  `toTargetGroup : group →* H`;
* a cover `cover : Action Z.Etale group` with a proof
  `isFiniteGeometricTorsor` that it is a finite geometric torsor over `Z`;
* a morphism `toSource : cover.V ⟶ (f^* Y).V` of etale `Z`-schemes, with
  `toSource_comm`: it intertwines `cover.ρ h` and `(f^* Y).ρ (toSourceGroup h)`;
* a morphism `toTarget : cover.V ⟶ Y'.V`, with `toTarget_comm`: it intertwines
  `cover.ρ h` and `Y'.ρ (toTargetGroup h)`;
* a module map `coefficient : M.V ⟶ M'.V`, with `coefficient_comm`: it
  intertwines `M.ρ (toSourceGroup h)` and `M'.ρ (toTargetGroup h)`.

`toSourceHom`, `toTargetHom` and `coefficientHom` package these as equivariant
maps `cover ⟶ (f^* Y)|_group`, `cover ⟶ Y'|_group` and
`M|_group ⟶ M'|_group`. The datum stores no sheaf, sheaf map or cohomology.

`isIso_targetComparison` shows that `K(toTargetHom, 𝟙)` is an isomorphism
`L_Z(Y', M') ⟶ L_Z(cover, M'|_group)` when `Y'` is a finite geometric torsor
over `Z`. It is `etaleAssociatedCoverComparison` applied to the two torsors
`Y'` and `cover`. `hom_ext` deduces that two morphisms into `L_Z(Y', M')` are
equal once they agree after `ι_Y'(M') ≫ cP(toTarget)`. The proof rewrites this
composite as `K(toTargetHom, 𝟙) ≫ ι_cover` and cancels the monomorphism
`ι_cover` and the isomorphism `K(toTargetHom, 𝟙)`.

## The transport map

For etale `f` and a finite geometric torsor `Y'`, `sheafMap t hY'` is the
composite

```text
r_f L_X(Y, M) --λ_f(Y, M)--> L_Z(f^* Y, M) --K(toSourceHom, coefficientHom)-->
  L_Z(cover, M'|_group) --K(toTargetHom, 𝟙)⁻¹--> L_Z(Y', M').
```

`sheafMap_targetComparison` states the defining equation
`sheafMap ≫ K(toTargetHom, 𝟙) = λ_f(Y, M) ≫ K(toSourceHom, coefficientHom)`.
`sheafMap_inclusion` gives the description on sections over the common cover:

```text
sheafMap ≫ ι_Y'(M') ≫ cP(toTarget)
  = λ_f(Y, M) ≫ ι_{f^* Y}(M) ≫ cP(toSource)
      ≫ productSheaf(cover.V).map((constant Z).map coefficient).
```

By `hom_ext`, this equation determines `sheafMap`. Every law below is proved by
reducing both sides to this form and comparing morphisms of cover objects.
The deck-group homomorphisms of different data never have to be compared.

## Laws

* `sheafMap_eq_of_refines`: let `t₁` and `t₂` be two data with the same
  `f, Y, Y', M, M'`. Suppose `w : t₁.cover.V ⟶ t₂.cover.V` satisfies
  `w ≫ t₂.toSource = t₁.toSource` and `w ≫ t₂.toTarget = t₁.toTarget`, and
  `t₁.coefficient = t₂.coefficient`. Then the two transport maps are equal. The
  map `w` need not be equivariant. The proof uses `coverPullback_comp` and the
  naturality `coverPullback_natural`.
* `sheafMap_eq_nsmul_of_refines`: with the same cover hypotheses and
  `t₁.coefficient = n • t₂.coefficient` for `n : ℕ`, the transport map of `t₁`
  is `n` times that of `t₂`. The proof also uses additivity of the constant
  sheaf functor (from Mathlib) and of `productSheaf`.
* `sheafMap_congr`: for `h : f₁ = f₂`, data `t₁` along `f₁` and `t₂` along `f₂`
  related by such a `w`, the identification `EtalePullback.restrictionCongr R h`
  followed by the transport map of `t₂` is the transport map of `t₁`. In the
  source condition, `t₁.toSource` is followed by the `eqToHom` between the two
  base changes.
* `restriction_sheafMap_inclusion`: for a further etale `g : W ⟶ Z`, it gives
  the sections of `r_g(sheafMap) ≫ λ_g(Y', M')` over `g^* cover`, namely

  ```text
  r_g(sheafMap) ≫ λ_g(Y', M') ≫ ι_{g^* Y'}(M') ≫ cP(etaleCoverMapPullback g toTarget)
    = r_g(λ_f(Y, M)) ≫ λ_g(f^* Y, M) ≫ ι_{g^* f^* Y}(M)
        ≫ cP(etaleCoverMapPullback g toSource)
        ≫ productSheaf((g^* cover).V).map((constant W).map coefficient).
  ```

  The proof uses `etaleConstantAssociatedPullback_crossCover` for the target and
  source cross-cover maps, together with the defining equation of `sheafMap`.
  No invertibility after base change is needed.
* `sheafMap_id`: let `t` be a datum along `𝟙 X` from `(Y, M)` to itself with
  `t.toSource ≫ etaleTorsorPullbackIdMap X Y = t.toTarget` and
  `t.coefficient = 𝟙`. Then its transport map is the component of
  `EtalePullback.restrictionId`. The proof uses
  `etaleConstantAssociatedPullback_id`.
* `sheafMap_comp`: take data `t` along `f`, `t'` along `g` and `t''` along
  `g ≫ f`, from `(Y, M)` to `(Y', M')`, from `(Y', M')` to `(Y'', M'')`, and from
  `(Y, M)` to `(Y'', M'')`. Take morphisms
  `w : t''.cover.V ⟶ (g^* t.cover).V` and `w' : t''.cover.V ⟶ t'.cover.V`
  satisfying

  ```text
  w ≫ etaleCoverMapPullback g t.toTarget = w' ≫ t'.toSource,
  w' ≫ t'.toTarget = t''.toTarget,
  w ≫ etaleCoverMapPullback g t.toSource = t''.toSource ≫ etaleTorsorPullbackCompMap f g Y,
  t.coefficient ≫ t'.coefficient = t''.coefficient.
  ```

  Then

  ```text
  (EtalePullback.restrictionComp f _ g).hom.app _ ≫ t''.sheafMap
    = r_g(t.sheafMap) ≫ t'.sheafMap.
  ```

  The proof applies `hom_ext` for `t''` and uses
  `etaleConstantAssociatedPullback_comp` on the left. On the right it uses
  `sheafMap_inclusion` for `t'` and `restriction_sheafMap_inclusion` for `t`,
  and it moves coefficient maps past cover restrictions by
  `coverPullback_natural`.

The forms of `sheafMap_id`, `sheafMap_comp` and `sheafMap_congr` match the
identity and composition laws of `EtalePullback.CoefficientDiagram`, which are
stated with `restrictionId`, `restrictionComp` and `restrictionCongr`.

## Scope

This file provides the sheaf maps and their laws for arbitrary data. It does
not construct transport data for Harris's coefficient systems or for the CM
tower, and it does not pass to cohomology. Those steps are separate.
