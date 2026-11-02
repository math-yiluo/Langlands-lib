# The degree-zero base-change comparison for a module map into a pushforward

Author: Worker 950. The definitions and lemma statements follow the specification
of task `ee369beb-e857-47d5-8ed0-5aeb6f432bf6` (published by Worker 360 and
Worker 1098 for the parent task `5b778a75-e74b-4ae4-9232-6735e3eefa47`).

Module `Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOf`, namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. It imports only
`Langlands.AlgebraicGeometry.Modules.AffineDirectImageBaseChange`.

The Library's degree-zero base change map `pushforwardBaseChange` is built from the
unit `P ⟶ p_* p^* P` of the pullback–pushforward adjunction. This module replaces
that unit by an arbitrary morphism `a : P ⟶ p_* N` and defines the resulting
comparison `b^* f_* P ⟶ f'_* N`, together with its ordinary-sections,
scalar-linear and tilde versions over spectra. It proves that the unit recovers
the published maps, that the published map followed by a pushforward is an
instance of the new one, and the evaluation and tilde formulas of the published
affine comparison, now for arbitrary `a`.

Nothing else is assumed or claimed. The square need not be cartesian. No morphism
is assumed flat, affine, quasi-compact or separated, and `X` and `X'` need not be
affine. No module is assumed quasi-coherent, and no comparison is claimed to be
an isomorphism. A criterion for invertibility is a separate later statement and is
not part of this module. The file has no proof holes and no axioms. It sets the
same three `backward.*` elaboration options as its sibling
`AffineDirectImageBaseChange`.

## Notation

For a morphism of schemes `h`, `h_*` is Mathlib's `Scheme.Modules.pushforward h`,
`h^*` is Mathlib's `Scheme.Modules.pullback h`, and `h^* ⊣ h_*` is Mathlib's
`Scheme.Modules.pullbackPushforwardAdjunction h`. Its unit at `P` is written
`η^h_P : P ⟶ h_* h^* P`, and `homEquiv` is its hom-set bijection
`(h^* A ⟶ B) ≃ (A ⟶ h_* B)`.

## Square layer

Setting: `X Y X' Y' : Scheme.{u}` for an arbitrary universe `u`, morphisms
`f : X ⟶ Y`, `b : Y' ⟶ Y`, `f' : X' ⟶ Y'`, `p : X' ⟶ X`, and a proof
`w : p ≫ f = f' ≫ b` that the square commutes:

```text
X' --p--> X
|         |
f'        f
v         v
Y' --b--> Y
```

The modules are `P : X.Modules` and `N : X'.Modules` (implicit arguments), and
`a : P ⟶ p_* N` is an arbitrary morphism.

The Library's `pushforwardSquareIso b f f' p w : p_* ⋙ f_* ≅ f'_* ⋙ b_*`
(module `DerivedRestriction`) is the composite of Mathlib's `pushforwardComp`,
`pushforwardCongr w` and the inverse `pushforwardComp`. Write `σ` for its `hom`.

### `pushforwardBaseChangeOf f b f' p w a`

```lean
pushforwardBaseChangeOf f b f' p w a :
  (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj P) ⟶
    (Scheme.Modules.pushforward f').obj N
```

It is the inverse of `homEquiv` for `b^* ⊣ b_*`, applied to

`f_*.map a ≫ σ.app N : f_* P ⟶ f_* p_* N ⟶ b_* f'_* N`.

So it is the adjunct `b^* f_* P ⟶ f'_* N` of that composite.

### `pushforwardBaseChangeOf_homEquiv` (simp)

`homEquiv` for `b` sends `pushforwardBaseChangeOf f b f' p w a` to
`f_*.map a ≫ σ.app N`. Proof: `Equiv.apply_symm_apply`.

### `pushforwardBaseChangeOf_unit`

For `P : X.Modules`,

`pushforwardBaseChangeOf f b f' p w (η^p_P) = pushforwardBaseChange b f f' p w P`,

where the right side is the Library's published map (module `DerivedRestriction`).
It is the inverse `homEquiv` of `f_*.map (η^p_P) ≫ σ.app (p^* P)`. Here
`N = p^* P`. The two sides are the same term, so the proof is `rfl`.

### `pushforwardBaseChange_comp_pushforward_map`

For `P : X.Modules`, `N : X'.Modules` and `ψ : p^* P ⟶ N`,

`pushforwardBaseChange b f f' p w P ≫ f'_*.map ψ =
  pushforwardBaseChangeOf f b f' p w (η^p_P ≫ p_*.map ψ)`.

Proof. Apply the injective `homEquiv` for `b`. Mathlib's
`Adjunction.homEquiv_naturality_right` turns the left side into
`homEquiv (pushforwardBaseChange …) ≫ b_*.map (f'_*.map ψ)`. Rewriting the
published map as `pushforwardBaseChangeOf` of the unit and using
`pushforwardBaseChangeOf_homEquiv` on both sides, it remains to show

`(f_*.map η^p_P ≫ σ.app (p^* P)) ≫ b_*.map (f'_*.map ψ) =
  f_*.map (η^p_P ≫ p_*.map ψ) ≫ σ.app N`.

This follows from functoriality of `f_*` and the naturality of `σ` at `ψ`.

## Spectra layer

Setting: `X X' : Scheme.{u}`, `R T : CommRingCat.{u}`, a ring map `φ : R ⟶ T`,
morphisms `f : X ⟶ Spec R`, `f' : X' ⟶ Spec T` and `g : X' ⟶ X`, and a proof
`w : g ≫ f = f' ≫ Spec.map φ`. This is the square layer with `Y = Spec R`,
`Y' = Spec T`, `b = Spec.map φ` and `p = g`. Again `P : X.Modules` and
`N : X'.Modules` are implicit, and `a : P ⟶ g_* N` is arbitrary.

Library ingredients:

- `relativeGlobalSections f : X.Modules ⥤ ModuleCat R` is
  `f_* ⋙ moduleSpecΓFunctor`: global sections of `f_* P` over `Spec R`, that is
  `Γ(X, P)` with its `R`-module structure (module `DerivedSections`).
- `relativeGlobalSectionsCompIso g f :
  g_* ⋙ relativeGlobalSections f ≅ relativeGlobalSections (g ≫ f)`
  (module `PushforwardComparison`).
- `relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w :
  relativeGlobalSections f' ⋙ ModuleCat.restrictScalars φ.hom ≅
  relativeGlobalSections (g ≫ f)` (module `DerivedBaseChange`).
- `tilde`, `tilde.map`, `tilde.toOpen` and the counit
  `Q.fromTildeΓ : tilde Γ(Spec T, Q) ⟶ Q` for `Q : (Spec T).Modules` are
  Mathlib's (`AlgebraicGeometry/Modules/Tilde.lean`).
- `tildePullbackIso φ M : (Spec.map φ)^* (tilde M) ≅ tilde (T ⊗[R] M)` and
  `tildePullback_hom_ext` are the Library's (module `TildePullback`).

### `sectionsBaseChangeMapOf φ f f' g w a`

The `R`-linear map

`(relativeGlobalSections f).obj P ⟶
  (ModuleCat.restrictScalars φ.hom).obj ((relativeGlobalSections f').obj N)`

given by `(relativeGlobalSections f).map a`, then
`(relativeGlobalSectionsCompIso g f).hom.app N`, then
`(relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w).inv.app N`.

### `scalarSectionsBaseChangeMapOf φ f f' g w a`

The `T`-linear map

`(ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj P) ⟶
  (relativeGlobalSections f').obj N`

that is the adjunct of `sectionsBaseChangeMapOf φ f f' g w a` under Mathlib's
`ModuleCat.extendRestrictScalarsAdj φ.hom` (extension of scalars is left adjoint
to restriction of scalars). The simp lemma
`scalarSectionsBaseChangeMapOf_homEquiv` states that this adjunction's `homEquiv`
sends it back to `sectionsBaseChangeMapOf φ f f' g w a`.

### `affineDirectImageTildeMapOf φ f f' g w a`

The morphism of `Spec T`-modules

`tilde (T ⊗[R] Γ(X, P)) ⟶ f'_* N`

given by `tilde.map (scalarSectionsBaseChangeMapOf φ f f' g w a)`, then the counit
`(f'_* N).fromTildeΓ`.

### Recovery of the published maps (`…Of_unit`)

For `M : X.Modules` and `a = η^g_M`:

- `sectionsBaseChangeMapOf_unit`: `sectionsBaseChangeMapOf φ f f' g w (η^g_M) =
  sectionsBaseChangeMap φ f f' g w M`;
- `scalarSectionsBaseChangeMapOf_unit`: the same for
  `scalarSectionsBaseChangeMap`;
- `affineDirectImageTildeMapOf_unit`: the same for `affineDirectImageTildeMap`.

The right sides are the published maps (modules `CohomologyBaseChangeZero` and
`AffineDirectImageBaseChange`). In each case the two sides are the same term, so
the proofs are `rfl`.

### `sectionsBaseChangeMapOf_apply`

For `x : (relativeGlobalSections f).obj P`,
`sectionsBaseChangeMapOf φ f f' g w a x = a.app ⊤ x`. Here `a.app ⊤` is the map
`Γ(X, P) ⟶ Γ(X', N)` on top sections. The composition and base-ring
identifications are the identity on underlying sections, so the proof is `rfl`.

### `scalarSectionsBaseChangeMapOf_one_tmul`

For `x : (relativeGlobalSections f).obj P`,
`scalarSectionsBaseChangeMapOf φ f f' g w a ((1 : T) ⊗ₜ[R,φ.hom] x) = a.app ⊤ x`.
Proof: evaluate `scalarSectionsBaseChangeMapOf_homEquiv` at `x`. Mathlib's
`ModuleCat.extendRestrictScalarsAdj_homEquiv_apply` says the `homEquiv` of a map
sends `x` to the map's value at `1 ⊗ x`. Then apply
`sectionsBaseChangeMapOf_apply`.

### `pushforwardBaseChangeOf_adjoint_app_top`

For `m : (relativeGlobalSections f).obj P`, the top-section component of the
`Spec.map φ`-adjoint of the comparison is the ordinary sections map:

`(homEquiv (pushforwardBaseChangeOf f (Spec.map φ) f' g w a)).app ⊤ m =
  sectionsBaseChangeMapOf φ f f' g w a m`,

where `homEquiv` is that of `(Spec.map φ)^* ⊣ (Spec.map φ)_*`. Proof: by
`pushforwardBaseChangeOf_homEquiv` the left side is
`(σ.app N).app ⊤ (a.app ⊤ m)`. The published
`pushforwardSquareIso_hom_app_top` (module `AffineDirectImageBaseChange`) says
`σ.app N` is the identity on top sections. The right side is `a.app ⊤ m` by
`sectionsBaseChangeMapOf_apply`.

### `pullback_fromTildeΓ_comp_pushforwardBaseChangeOf` (`@[reassoc]`)

```lean
(Scheme.Modules.pullback (Spec.map φ)).map
    ((Scheme.Modules.pushforward f).obj P).fromTildeΓ ≫
  pushforwardBaseChangeOf f (Spec.map φ) f' g w a =
(tildePullbackIso φ ((relativeGlobalSections f).obj P)).hom ≫
  affineDirectImageTildeMapOf φ f f' g w a
```

Both sides are morphisms `(Spec.map φ)^* (tilde Γ(X, P)) ⟶ f'_* N`. The source's
`fromTildeΓ` is the counit for `f_* P`. The `@[reassoc]` attribute also generates
`pullback_fromTildeΓ_comp_pushforwardBaseChangeOf_assoc`.

Proof. It follows the published `pullback_fromTildeΓ_comp_pushforwardBaseChange`,
with `a` in place of the unit. By `tildePullback_hom_ext` it suffices to compare
the two adjoints on the global generators `tilde.toOpen _ ⊤ m` for
`m ∈ Γ(X, P)`. Mathlib's `Adjunction.homEquiv_naturality_left` and
`homEquiv_naturality_right` move the outer factors out of the adjoints. On the
left, the counit sends the generator to `m` (Mathlib's
`Scheme.Modules.toOpen_fromTildeΓ_app`), and
`pushforwardBaseChangeOf_adjoint_app_top` gives `sectionsBaseChangeMapOf … a m`.
On the right, the Library's `tildePullbackIso_adjoint_toOpen_top` sends the
generator to the generator of `1 ⊗ m`. Mathlib's `tilde.toOpen_map_app` and the
counit over `Spec T` turn this into `scalarSectionsBaseChangeMapOf … a (1 ⊗ m)`.
That equals `a.app ⊤ m` by `scalarSectionsBaseChangeMapOf_one_tmul`, which is the
left side by `sectionsBaseChangeMapOf_apply`.

## Provenance

Internal. The source does not state these definitions or lemmas. They are a
formal adjunction generalization of the Library's published degree-zero base
change map `DerivedSections.pushforwardBaseChange`: the unit `η^p_P` of
`p^* ⊣ p_*` becomes an arbitrary morphism `a : P ⟶ p_* N`. The unit case is
`pushforwardBaseChangeOf_unit`, and the spectra-layer `…Of_unit` lemmas recover
`sectionsBaseChangeMap`, `scalarSectionsBaseChangeMap` and
`affineDirectImageTildeMap`.

Motivation: `pushforwardBaseChange` is the degree-zero base change map of The
Stacks Project, Cohomology of Sheaves, section "The base change map" (tag 02N6,
label `section-base-change-map`), file `cohomology.tex` lines 2954–3032 at Stacks
commit `a04446e57ec1fbc252a871afcec7752fb2807b14` (file SHA-256
`fa9747d0082afbf8b09244dcc6c260f8a122e5e3b4a3c69e2273506d76e18a42`, registered
source `stacks-flasque-affine-vanishing-kunneth-a04446e5`). This section includes
Lemma `lemma-base-change-map-flat-case` (tag 02N7) from line 2977. The tag-to-label
map is `tags.txt` lines 3469–3470 of the same commit.

The source's square has `g' : X' → X`, `f : X → S`, `f' : X' → S'` and
`g : S' → S`. In this module these are `p`, `f`, `f'` and `b`. The source assumes
`g` and `g'` flat and works with bounded below complexes in the derived category.
Its proof composes the adjunction map `F → g'_* g'^* F`, lifted to injective
resolutions, with `f_* g'_* = g_* f'_*`, and takes the adjunct under
`g^* ⊣ g_*`. In degree zero this is the adjunct of
`f_* F ⟶ f_* g'_* g'^* F = g_* f'_* g'^* F`, which is `pushforwardBaseChange`.
Here the first arrow may be any `a : P ⟶ p_* N`. No flatness or other
hypothesis of the source is used.

The parent task needs an arbitrary `a`. In the flat affine case it plans to apply
the comparison to the components of the Library chain map
`CechResolution.cechPullback` (module `CechResolution.BaseChange`). That chain map
is `cechPushforward` of the unit of `g^* ⊣ g_*`. Its components
`cechTermPushforward` are morphisms `P ⟶ g_* N` between Čech terms, and they are
not given as units of the adjunction. The lemma
`pushforwardBaseChange_comp_pushforward_map` connects a unit followed by a
pushforward with the published map.
