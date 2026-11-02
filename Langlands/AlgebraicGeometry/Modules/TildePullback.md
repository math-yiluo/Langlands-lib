# Pullback of an associated sheaf along a morphism of spectra

Fix a universe `u`, commutative rings `R A : CommRingCat.{u}` and a ring map
`φ : R ⟶ A`. Write `p := Spec.map φ : Spec A ⟶ Spec R`. For `M : ModuleCat.{u} R`, write
`M^~ := AlgebraicGeometry.tilde M` for the associated module sheaf on
`Spec R`, and `E := (ModuleCat.extendScalars φ.hom).obj M` for the scalar extension. In
Mathlib's convention `E` is `A ⊗[R] M`, with `A` on the left; its elements are written
`a ⊗ₜ[R, φ.hom] m`.

`Langlands.Scheme.Modules.tildePullbackIso φ M` is a canonical isomorphism

`(AlgebraicGeometry.Scheme.Modules.pullback p).obj (tilde M) ≅ tilde E`.

The existing Mathlib constructions of `tilde`, of module pullback and of scalar extension are
used unchanged. Nothing is assumed about `φ` or `M`: no flatness, finiteness, freeness, finite
presentation or nonzero rings. All declarations live in the namespace
`Langlands.Scheme.Modules` and are universe polymorphic in the single universe `u`.

## Construction

The isomorphism comes from uniqueness of left adjoints. It uses two adjunctions with the same
right adjoint `pushforward p ⋙ moduleSpecΓFunctor`. This right adjoint sends a module sheaf `N`
on `Spec A` to the `R`-module of global sections of `p_* N`.

- `pushforwardΓIso φ` is the natural isomorphism
  `pushforward p ⋙ moduleSpecΓFunctor ≅ moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom`.
  It identifies the global sections of `p_* N` with the global sections of `N`, viewed as an
  `R`-module through `φ`. It is Mathlib's `pushforwardCompModulesSpecToSheafIso φ`
  (in `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`) whiskered by evaluation of the
  underlying sheaf at the top open. Both of its components are the identity on elements
  (`pushforwardΓIso_hom_app_apply` and `pushforwardΓIso_inv_app_apply`, both by `rfl`).
- `tildePullbackAdjunction φ` is the composite adjunction
  `tilde.functor R ⋙ pullback p ⊣ pushforward p ⋙ moduleSpecΓFunctor`. It composes
  Mathlib's `tilde.adjunction` (`tilde.functor R ⊣ moduleSpecΓFunctor`, in
  `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`) with
  `Scheme.Modules.pullbackPushforwardAdjunction p` (`pullback p ⊣ pushforward p`, in
  `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`).
- `extendScalarsTildeAdjunction φ` is the composite adjunction
  `ModuleCat.extendScalars φ.hom ⋙ tilde.functor A ⊣ pushforward p ⋙ moduleSpecΓFunctor`.
  It composes Mathlib's `ModuleCat.extendRestrictScalarsAdj φ.hom` (in
  `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`) with `tilde.adjunction` for `A`.
  The resulting adjunction has right adjoint `moduleSpecΓFunctor ⋙ restrictScalars φ.hom`.
  `Adjunction.ofNatIsoRight` then transports it along `(pushforwardΓIso φ).symm`.
- `tildePullbackNatIso φ` is
  `(tildePullbackAdjunction φ).leftAdjointUniq (extendScalarsTildeAdjunction φ)`. This is a
  natural isomorphism `tilde.functor R ⋙ pullback p ≅ extendScalars φ.hom ⋙ tilde.functor A`
  of functors `ModuleCat R ⥤ (Spec A).Modules`.
- `tildePullbackIso φ M` is the component of `tildePullbackNatIso φ` at `M`.
  `tildePullbackNatIso_app` records this by `rfl`.

## Naturality

`tildePullbackIso_hom_naturality` states, for `f : M ⟶ N` in `ModuleCat R`:

`(pullback p).map (tilde.map f) ≫ (tildePullbackIso φ N).hom =
  (tildePullbackIso φ M).hom ≫ tilde.map ((extendScalars φ.hom).map f)`.

`tildePullbackIso_inv_naturality` is the same square for the inverses. Both lemmas carry
`@[reassoc]`. They are the naturality of `tildePullbackNatIso φ`.

## Generator formula

For a morphism `g : (pullback p).obj (tilde M) ⟶ N` with `N : (Spec A).Modules`,
`tildePullbackAdjoint φ g : tilde M ⟶ (pushforward p).obj N` is its adjoint under
`pullbackPushforwardAdjunction p`. This is an abbreviation for
`(pullbackPushforwardAdjunction p).homEquiv _ _ g`.

- `tildePullbackIso_adjoint_toOpen` is the generator formula on every open. Let
  `β := tildePullbackAdjoint φ (tildePullbackIso φ M).hom`. Then for every
  `U : (Spec R).Opens` and `m : M`,

  `β.app U (tilde.toOpen M U m) = tilde.toOpen E (p ⁻¹ᵁ U) ((1 : A) ⊗ₜ[R, φ.hom] m)`.

  Here `tilde.toOpen M U : M ⟶ Γ(M^~, U)` is Mathlib's map to sections. Sections of `p_* (tilde E)`
  over `U` are sections of `tilde E` over `p ⁻¹ᵁ U` by definition.
- `tildePullbackIso_adjoint_toOpen_top` is the case `U = ⊤`, where the target open is written
  `⊤` instead of `p ⁻¹ᵁ ⊤`.
- `tildePullback_hom_ext` is an extensionality principle. Two morphisms
  `g₁ g₂ : (pullback p).obj (tilde M) ⟶ N` are equal if their adjoints agree on all global
  generators `tilde.toOpen M ⊤ m`, for `m : M`.

These lemmas characterize the forward map of the actual isomorphism `tildePullbackIso φ M`.
With `tildePullback_hom_ext` they let one identify a morphism out of `p^*(M^~)`, for example one
induced by a derivation, by computing its adjoint on the elements `tilde.toOpen M ⊤ m`.

## Algebra form

Section `Algebra` restates the isomorphism with Mathlib's algebra tensor product. Here
`A B : CommRingCat.{u}` carry an instance `[Algebra A B]`, and `M : ModuleCat.{u} A`. Write
`q := Spec.map (CommRingCat.ofHom (algebraMap A B))`.

The underlying tensor comparison is imported from
[ExtendScalarsTensor](../../Algebra/ExtendScalarsTensor.md). Its two additive
maps, `extendScalarsAlgebraEquiv`, `extendScalarsAlgebraIso` and the pure-tensor
formula retain their published names and implementations in
`Langlands.Scheme.Modules`. They identify scalar extension along
`φ := CommRingCat.ofHom (algebraMap A B)` with `B ⊗[A] M`.

- `tildePullbackAlgebraIso A B M` is the composite isomorphism
  `tildePullbackIso φ M ≪≫ (tilde.functor B).mapIso (extendScalarsAlgebraIso A B M)`, of type

  `(pullback q).obj (tilde M) ≅ tilde (ModuleCat.of B (B ⊗[A] M))`.
- `tildePullbackAlgebraIso_adjoint_toOpen` is its generator formula on every open. For
  `U : (Spec A).Opens` and `m : M`,

  `(tildePullbackAdjoint φ (tildePullbackAlgebraIso A B M).hom).app U (tilde.toOpen M U m) =
    tilde.toOpen (ModuleCat.of B (B ⊗[A] M)) (q ⁻¹ᵁ U) ((1 : B) ⊗ₜ[A] m)`.

## Proofs

- Top formula. Mathlib's `Adjunction.homEquiv_leftAdjointUniq_hom_app` says that the adjoint of
  `tildePullbackIso φ M` under `tildePullbackAdjunction φ` is the unit of
  `extendScalarsTildeAdjunction φ` at `M`. The adjoint under the composite adjunction is the
  `tilde.adjunction` adjoint of `β`. Evaluated at `m`, it is `β.app ⊤ (tilde.toOpen M ⊤ m)`,
  because the unit of `tilde.adjunction` is `tilde.toOpen M ⊤`. The unit of the second
  adjunction sends `m` to `tilde.toOpen E ⊤ (1 ⊗ₜ m)`. It is the unit `m ↦ 1 ⊗ₜ m` of
  `extendRestrictScalarsAdj`, followed by the `tilde.adjunction` unit for `E` and the
  identity-on-elements `pushforwardΓIso`. The lemma applies this equality of linear maps to `m`.
  The remaining identifications hold by definitional unfolding.
- All-open formula. Restriction along `U ≤ ⊤` commutes with `β`, by naturality of the underlying
  presheaf morphism `β.mapPresheaf`. Mathlib's `tilde.toOpen_res` says that restriction sends
  `tilde.toOpen M ⊤ m` to `tilde.toOpen M U m` in the source. In the target it sends
  `tilde.toOpen E ⊤ (1 ⊗ₜ m)` to `tilde.toOpen E (p ⁻¹ᵁ U) (1 ⊗ₜ m)`. Lean checks both
  restriction identities by definitional unfolding (`change`) rather than by an explicit
  rewrite with `toOpen_res`. The lemma then follows from the top formula.
- Extensionality. The map `g ↦ tildePullbackAdjoint φ g` is the bijection `homEquiv` of
  `pullbackPushforwardAdjunction p`. Then `tilde.adjunction.homEquiv`, by
  `Adjunction.homEquiv_unit`, is precomposition with the unit `tilde.toOpen M ⊤`. Both maps are
  injective, so equality on the elements `tilde.toOpen M ⊤ m` suffices, by extensionality of
  linear maps.
- Algebra-form generator formula. `Adjunction.homEquiv_naturality_right` rewrites the adjoint of
  the composite as the adjoint `β` of `tildePullbackIso φ M`, followed by the pushforward of
  `tilde.map (extendScalarsAlgebraIso A B M).hom`. On sections over `U`, that pushforward is
  the section map of `tilde.map` over `q ⁻¹ᵁ U` (a `change`). The all-open formula computes
  `β` on `tilde.toOpen M U m`. Mathlib's `tilde.toOpen_map_app` then moves the module map inside
  `tilde.toOpen`, and `1 ⊗ₜ[A, φ.hom] m ↦ 1 ⊗ₜ[A] m` holds definitionally.

## Provenance and scope

This is internal infrastructure assembled from pinned Mathlib
(commit `5ed2965256430c3649e86755f9576b54eca72435`). It is not a new translation of a literature
definition. It formalizes the standard fact that pulling back the sheaf associated with an
`R`-module along `Spec A → Spec R` gives the sheaf associated with its scalar extension to `A`.
The reference statement is the Stacks Project,
[Lemma 26.7.3(1), Tag 01I9](https://stacks.math.columbia.edu/tag/01I9), which uses the same
left-factor scalar-extension convention. Its associated-sheaf mapping property is
[Lemma 26.7.1, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7), with arbitrary target module
sheaves. The registered source is `stacks-affine-tilde-pullback-2026-10-25`, fingerprint
`80ddd071d3f45b209a6204de561156005e3e62a96f9365a7d3551c55449c6e18`; the original snapshots are
`01I9.html` and `01I7.html` in
`literature/Stacks Project - Associated module sheaves and affine pullback (HTML snapshot 2026-10-25)/`.
Neither per-tag page has comments. These statements impose no nonzero-ring or finiteness
assumption. The Lean proof uses the adjunction construction described above rather than
translating the Stacks proof.

The construction is the uniqueness-of-left-adjoints argument suggested by the task. The
canonical global-sections identification is supplied by Mathlib's
`pushforwardCompModulesSpecToSheafIso`.

Worker 274 authored the reused complete Lean construction and its explanation; Worker 405
checked the draft in the approved environment, verified the source correspondence, and
prepared this submission.

The local option `backward.isDefEq.respectTransparency false` permits elaboration across
Mathlib's scheme-module wrappers. It adds no mathematical assumption. The module imports
`Mathlib.AlgebraicGeometry.Modules.Tilde` and the extracted pure algebra
comparison `Langlands.Algebra.ExtendScalarsTensor`. It does not use relative differentials or
differential base change, and it proves nothing about them.
