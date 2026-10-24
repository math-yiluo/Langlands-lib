# Pullback of finite étale covers and functoriality of geometric fundamental groups

This module constructs pullback of actual finite étale covers along a morphism of
schemes. It compares the pointed fibre functors and induces a continuous
homomorphism of the fundamental groups from
`Langlands.AlgebraicGeometry.FiniteEtale.Definitions`. All declarations are in
the namespace `Langlands.AlgebraicGeometry.FiniteEtale` and reuse the existing
`Cover`, `Fiber`, `pointFunctor`, `fiberFunctor` and `FundamentalGroup`. No
abstract replacement category, Galois-category theorem or new axiom is used.

## Source and scope

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary version, Chapter X, (10.30) "Functoriality", printed p.151
(PDF p.155). The composition law is the first sentence of printed p.152
(PDF p.156). The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

In the source, `f : Y → X` is a morphism of connected, locally noetherian
schemes, `ȳ` is a geometric point of `Y` and `x̄ = f(ȳ)`. Sending an étale
covering `X′ → X` to `X′ ×_X Y → Y` gives a functor `f^* : FEt_X → FEt_Y`
with `F_x̄ = F_ȳ ∘ f^*`. Every automorphism of `F_ȳ` therefore induces one of
`F_x̄`, giving a canonical homomorphism `f_* : π₁(Y, ȳ) → π₁(X, x̄)`. For a
second morphism `g : Z → Y`, the source states `(f ∘ g)_* = f_* ∘ g_*`.

The Lean notation is as follows. The source's `X`, `Y`, `Z` are `S`, `S'`,
`S''`. Its `f` is `f : S' ⟶ S` and its `g` is `g : S'' ⟶ S'`. Its points
`x̄`, `ȳ` are `s : Spec Ω ⟶ S` and `t : Spec Ω ⟶ S'`, a point of `S''` is
`u : Spec Ω ⟶ S''`, and `f^*` is `pullbackFunctor f`.

### Hypotheses

The Lean constructions are more general than the source's setting:

- `f` is an arbitrary morphism in `Scheme.{u}`. Connectedness and local
  noetherianity of `S` or `S'` are never assumed.
- `Ω : Type u` is an arbitrary field. Algebraic closure is not assumed.
- Instead of fixing `s := t ≫ f`, the fibre constructions take `s` together
  with an explicit point equation `h : t ≫ f = s`. The source's case is
  `s := t ≫ f`, `h := rfl`. With this form the identity and composition laws
  need no transport along equalities of points.
- As in `Definitions`, the finite-fibre hypotheses
  `hs : ∀ Y : Cover S, Finite (Fiber s Y)` and
  `ht : ∀ Y : Cover S', Finite (Fiber t Y)` are explicit parameters wherever
  `fiberFunctor` or `FundamentalGroup` appears. They are needed only for
  finite-set packaging, and the constructions do not depend on which proofs are
  supplied.

In the source's geometric application, `Ω` is algebraically closed and both
schemes are connected and locally noetherian. The published theorem
`geometricFiberFinite` (module
`Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof`) can then
supply `hs` and `ht`. This module does not import it, and none of its results
depend on connectedness, local noetherianity, algebraic closure, or Grothendieck's
Theorem (10.28). The source's equality `F_x̄ = F_ȳ ∘ f^*` is realized as an
explicit canonical natural isomorphism; the underlying functors are not equal.

The remaining claims of (10.30) on printed p.152 are not formalized here. These
are the isomorphism `π₁(Y, ȳ) ≅ Stab(ȳ)` for an étale covering `f`, and the
correspondence between pointed connected coverings and open subgroups. The
module also contains no base-point change (10.29), geometric-path existence or
Tate-module transport.

### Provenance

The pullback functor, the fibre comparison, the induced homomorphism and the
composition law are those of (10.30). The source leaves the following as
implicit standard facts, and they are derived here: the explicit object and
morphism formulas, the identity and composition comparison isomorphisms of
pullback functors, the fibre bijection as an explicit universal-property map,
the identity law, the evaluation and characterization formulas, and
continuity. The proofs are elementary manipulations of Mathlib's pullbacks,
slice categories, `Iso.conjAut` and evaluation topology. They are described
below.

## The pullback functor

`pullbackFunctor f : Cover S ⥤ Cover S'` sends a cover `Y` to the second
projection `pullback.snd Y.obj.hom f : pullback Y.obj.hom f ⟶ S'`. This is
Mathlib's actual scheme fibre product `Y ×_S S'`. Finiteness and étaleness of
the projection are Mathlib's base-change instances. A morphism of covers `k`
goes to

```lean
pullback.lift (pullback.fst Y.obj.hom f ≫ k.hom.left) (pullback.snd Y.obj.hom f) _
```

that is, `(y, s′) ↦ (k y, s′)`. The functor laws are proved by extensionality in
the full subcategory and the slice, followed by `pullback.hom_ext` and `simp`.

The recorded formulas are as follows.

- `pullbackFunctor_obj_obj`, `pullbackFunctor_obj_left`,
  `pullbackFunctor_obj_hom` give the object formula.
- `pullbackFunctor_map_hom_left` gives the morphism formula.
  `pullbackFunctor_map_hom_left_fst` and `pullbackFunctor_map_hom_left_snd`
  give its two projections, `pullback.fst ≫ k.hom.left` and `pullback.snd`.
- `pullbackFunctor_comp_inclusion` states that
  `pullbackFunctor f ⋙ inclusion S' = inclusion S ⋙ Over.pullback f` holds by
  `rfl`. Forgetting finite étaleness thus gives exactly Mathlib's slice
  pullback functor.

### Identity and composition

- `pullbackIdIso S : pullbackFunctor (𝟙 S) ≅ 𝟭 (Cover S)` has components the
  first projection `pullback.fst Y.obj.hom (𝟙 S)`, with inverse
  `pullback.lift (𝟙 _) Y.obj.hom _`. The component formulas are
  `pullbackIdIso_hom_app_hom_left` and `pullbackIdIso_inv_app_hom_left`.
  Naturality is `pullbackFunctor_map_hom_left_fst`.
- `pullbackCompIso f g : pullbackFunctor (g ≫ f) ≅ pullbackFunctor f ⋙ pullbackFunctor g`
  has components the inverse of Mathlib's pasting isomorphism
  `pullbackLeftPullbackSndIso Y.obj.hom f g`, as recorded by
  `pullbackCompIso_hom_app_hom_left`. Naturality is proved by `pullback.hom_ext`
  on the iterated pullback and the morphism formula.
  `pullbackCompIso_inv_app_hom_left` identifies the inverse component as
  `pullback.lift (pullback.fst _ g ≫ pullback.fst Y.obj.hom f) (pullback.snd _ g) _`,
  that is, `((y, s′), s″) ↦ (y, s″)`.

These isomorphisms are built directly from projections, not from Mathlib's
`Over.pullbackId` and `Over.pullbackComp`, which are defined through
adjunction conjugation.

## Fibre comparison

Fix `f : S' ⟶ S`, points `t : Spec Ω ⟶ S'` and `s : Spec Ω ⟶ S`, and
`h : t ≫ f = s`.

`pullbackFiberEquiv f t s h Y : Fiber s Y ≃ Fiber t ((pullbackFunctor f).obj Y)`
is given by the universal property of the pullback. It is not supplied data:

- a lift `x` of `s` goes to `pullback.lift x.left t _`, whose commutativity
  proof is the slice equation of `x` rewritten by `h`
  (`pullbackFiberEquiv_apply_left`);
- a lift `y` of `t` goes back to `y.left ≫ pullback.fst Y.obj.hom f`
  (`pullbackFiberEquiv_symm_apply_left`).

One inverse law is `pullback.lift_fst`. The other uses `pullback.hom_ext`, with
the slice equation `y.left ≫ pullback.snd = t` for the second projection.
`pullbackFiberEquiv_apply_left_fst` and `pullbackFiberEquiv_apply_left_snd`
record the projections `x.left` and `t` of the image.
`pullbackFiberEquiv_apply_left_eq` is the uniqueness clause: every morphism
`z : Spec Ω ⟶ pullback Y.obj.hom f` with these two projections equals the
image of `x`.

`pullbackFiberFinite f t s h` derives `∀ Y : Cover S, Finite (Fiber s Y)` from
`∀ Y : Cover S', Finite (Fiber t Y)` through these bijections.

### Natural isomorphisms of fibre functors

- `pointFunctorPullbackIso f t s h : pointFunctor s ≅ pullbackFunctor f ⋙ pointFunctor t`
  has components `pullbackFiberEquiv f t s h Y`, as recorded by
  `pointFunctorPullbackIso_hom_app` and `pointFunctorPullbackIso_inv_app`.
  Naturality, for postcomposition by a cover morphism `g`, is checked on both
  pullback projections.
- `fiberFunctorPullbackIso f t s h hs ht : fiberFunctor s hs ≅ pullbackFunctor f ⋙ fiberFunctor t ht`
  is the same family, regarded as isomorphisms of finite sets. Its components
  are recorded by `fiberFunctorPullbackIso_hom_app` and
  `fiberFunctorPullbackIso_inv_app`.
  `fiberFunctorPullbackIso_comp_incl` states that whiskering by
  `FintypeCat.incl` recovers `pointFunctorPullbackIso`. This is the source's
  `F_x̄ = F_ȳ ∘ f^*` with `x̄ = s` and `ȳ = t`.

### Coherence of fibre bijections

- `pullbackFiberEquiv_id_left`: for `h : t ≫ 𝟙 S = t`, composing the image of
  `x` with the component of `pullbackIdIso S` returns `x.left`.
- `pullbackFiberEquiv_comp_left`: for `g : S'' ⟶ S'`, `u : Spec Ω ⟶ S''`,
  `hg : u ≫ g = t` and `hgf : u ≫ g ≫ f = s`, the iterated bijection (first
  along `f`, then along `g`) followed by the inverse component of
  `pullbackCompIso f g` is the bijection along `g ≫ f`. The proof uses the
  uniqueness clause and `pullbackCompIso_inv_app_hom_left`.

## The induced homomorphism

`fundamentalGroup_ext` proves that two elements of `FundamentalGroup s hs` are
equal when they act equally on every fibre `Fiber s Y`.

`fundamentalGroupMap f t s h ht hs : FundamentalGroup t ht →* FundamentalGroup s hs`
is the source's `f_*`. It is the composite of two homomorphisms:

1. whiskering an automorphism of `fiberFunctor t ht` by `pullbackFunctor f`, the
   `mapAut` of `(Functor.whiskeringLeft _ _ FintypeCat).obj (pullbackFunctor f)`;
2. conjugation `Iso.conjAut` along `(fiberFunctorPullbackIso f t s h hs ht).symm`.

`fundamentalGroupMap_apply` states the result as the natural isomorphism

```lean
fiberFunctorPullbackIso f t s h hs ht ≪≫ Functor.isoWhiskerLeft (pullbackFunctor f) σ ≪≫
  (fiberFunctorPullbackIso f t s h hs ht).symm
```

### Evaluation formula

- `fundamentalGroupMap_smul` proves, by `rfl`,
  `fundamentalGroupMap f t s h ht hs σ • x = (pullbackFiberEquiv f t s h Y).symm (σ • pullbackFiberEquiv f t s h Y x)`.
  The image of `σ` moves `x` to the pulled-back fibre, applies `σ` there, and
  moves the result back.
- `pullbackFiberEquiv_smul` is the equivalent equivariance statement.
- `fundamentalGroupMap_smul_left` gives the underlying morphism
  `(σ • pullbackFiberEquiv f t s h Y x).left ≫ pullback.fst Y.obj.hom f`.
- `fundamentalGroupMap_smul_left_of_comp` characterizes the action through any
  compatible morphism. Let `Y'` be a cover of `S'`, `y ∈ Fiber t Y'`, and
  `φ : Y'.obj.left ⟶ Y.obj.left` with `φ ≫ Y.obj.hom = Y'.obj.hom ≫ f` and
  `y.left ≫ φ = x.left`. Then
  `(fundamentalGroupMap f t s h ht hs σ • x).left = (σ • y).left ≫ φ`.
  For the proof, `φ` and `Y'.obj.hom` induce a cover morphism
  `ψ : Y' ⟶ (pullbackFunctor f).obj Y`. By the uniqueness clause,
  `pullbackFiberEquiv f t s h Y x = y ≫ ψ.hom`. Naturality of the action
  (`smul_naturality` from `Definitions`) and `pullback.lift_fst` then conclude.

### Identity and composition laws

The point equations are explicit hypotheses.

- `fundamentalGroupMap_id`: for `t : Spec Ω ⟶ S` and `h : t ≫ 𝟙 S = t`,
  `fundamentalGroupMap (𝟙 S) t t h ht ht = MonoidHom.id _`. The proof applies
  `fundamentalGroup_ext` and the characterization with `φ = 𝟙`.
- `fundamentalGroupMap_comp`: for `g : S'' ⟶ S'`, `u : Spec Ω ⟶ S''`,
  `hg : u ≫ g = t`, `hgf : u ≫ g ≫ f = s`, and finite fibres `hu` at `u`,
  ```lean
  fundamentalGroupMap (g ≫ f) u s hgf hu hs =
    (fundamentalGroupMap f t s h ht hs).comp (fundamentalGroupMap g u t hg hu ht)
  ```
  This is the source's `(f ∘ g)_* = f_* ∘ g_*`. The proof applies the
  characterization to the composite `g ≫ f`. It takes as the point the
  iterated fibre bijection of `x`, and as `φ` the composite of first
  projections `pullback.fst _ g ≫ pullback.fst Y.obj.hom f`, which is the
  inverse component of `pullbackCompIso f g` followed by the first projection.
  Two applications of `fundamentalGroupMap_smul_left` then rewrite the
  right-hand side to the same morphism.

### Continuity

The topology on `FundamentalGroup` is the existing one from `Definitions`. It is
induced by Mathlib's `PreGaloisCategory.autEmbedding` into the product over all
covers of the finite discrete fibre automorphism groups.
`continuous_fundamentalGroupMap` proves that `fundamentalGroupMap f t s h ht hs`
is continuous. Because `autEmbedding` is a closed embedding, hence inducing, it
suffices to check each coordinate at a cover `Y`. That coordinate is evaluation
at `(pullbackFunctor f).obj Y`, followed by conjugation by the fixed component
of `fiberFunctorPullbackIso` at `Y`. Evaluation is continuous for the induced
product topology, and conjugation has a discrete domain. The argument follows
Mathlib's `continuous_mapAut_whiskeringRight`.

`fundamentalGroupContinuousMap f t s h ht hs : FundamentalGroup t ht →ₜ* FundamentalGroup s hs`
bundles the homomorphism with this continuity proof.
`fundamentalGroupContinuousMap_apply` identifies its underlying map.
