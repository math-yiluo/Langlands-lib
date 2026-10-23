# Canonical tensor comparisons for presheaf-module pullback

For schemes `X Y : AlgebraicGeometry.Scheme.{u}` and an arbitrary scheme
morphism `f : X ⟶ Y`, this module constructs the natural maps

```
U(P) ⊗ U(Q) ⟶ U(P ⊗ Q)
L(M ⊗ N) ⟶ L(M) ⊗ L(N),
```

where `U` and `L` are Mathlib's presheaf-module pushforward and its left
adjoint. All declarations lie in `Langlands.Scheme.Modules`. Tensor
products are sectionwise tensor products of presheaves of modules, using
Mathlib's monoidal structure on `PresheafOfModulesOfCommRing`. There are no
flatness, finite generation, or local freeness assumptions.

This is a construction and basic-laws unit. It proves neither invertibility
nor monoidal coherence of pullback and installs no monoidal pullback instance.

## The functors and adjunction

The abbreviations `presheafPushforward f`, `presheafPullback f`, and
`presheafPullbackPushforwardAdjunction f` expose respectively
`PresheafOfModules.pushforward`, `PresheafOfModules.pullback`, and
`PresheafOfModules.pullbackPushforwardAdjunction` with module universe `u`,
the functor `TopologicalSpace.Opens.map f.base`, and ring-presheaf morphism

```
CategoryTheory.Functor.whiskerRight f.c (forget₂ CommRingCat RingCat).
```

The ring presheaves are explicitly `X.ringCatSheaf.obj` and
`Y.ringCatSheaf.obj`. This morphism is definitionally the `.hom` of
`f.toRingCatSheafHom`. The adjunction is Mathlib's existing adjunction;
no additional adjoint or comparison is assumed. Its unit is denoted by `η`
below, and its counit by `ε`.

A local instance exposes Mathlib's sectionwise monoidal structure on the
definitionally equal category `X.PresheafOfModules`. The elaboration option
`backward.isDefEq.respectTransparency false` permits Lean to unfold these
category presentations during elaboration; it adds no mathematical assumption.

## Pushforward

Let `V : Y.Opensᵒᵖ` and write `F(V)` for
`(TopologicalSpace.Opens.map f.base).op.obj V`. Put
`R = Y.presheaf.obj V` and `S = X.presheaf.obj (F(V))`.
The component of `presheafPushforwardTensorApp f P Q` at `V` is the map

```
P(F(V)) ⊗_R Q(F(V)) ⟶ P(F(V)) ⊗_S Q(F(V))
```

sending `p ⊗ q` to `p ⊗ q`, with the modules viewed over `R` by restriction
of scalars along `(f.c.app V).hom : R →+* S`. It is built by applying the
published `restrictScalarsTensorLift` to the identity of the sectionwise
`S`-tensor product. Thus it is a well-defined `R`-linear map.

`presheafPushforwardTensorApp_app_tmul` proves this formula by definition.
The restriction compatibility required for a presheaf morphism is proved
by tensor extensionality: both sides send `p ⊗ q` to the tensor of the two
restricted sections.

`presheafPushforwardTensorApp_naturality` states that, for `a : P ⟶ P'`
and `b : Q ⟶ Q'`,

```
(U.map a ⊗ₘ U.map b) ≫ presheafPushforwardTensorApp f P' Q' =
  presheafPushforwardTensorApp f P Q ≫ U.map (a ⊗ₘ b).
```

Its proof applies presheaf extensionality and then tensor extensionality;
the resulting equality on pure tensors is definitional.
`presheafPushforwardTensor f` packages the components as the natural
transformation from `U.prod U ⋙ MonoidalCategory.tensor Y.PresheafOfModules`
to `MonoidalCategory.tensor X.PresheafOfModules ⋙ U`.
`presheafPushforwardTensor_app` identifies its components by definition.

## Pullback

`presheafPullbackTensorComparisonApp f M N` is the inverse image under the
adjunction bijection

```
Hom(L(M ⊗ N), L(M) ⊗ L(N)) ≃ Hom(M ⊗ N, U(L(M) ⊗ L(N)))
```

of the composite

```
M ⊗ N --η_M ⊗ₘ η_N--> U(L(M)) ⊗ U(L(N))
  --presheafPushforwardTensorApp f (L(M)) (L(N))--> U(L(M) ⊗ L(N)).
```

`homEquiv_presheafPullbackTensorComparisonApp` proves that this is exactly
the adjunction image, by the inverse law of the equivalence.
`homEquiv_presheafPullbackTensorComparisonApp_app_tmul` evaluates that image
at `V`: it sends `m ⊗_R n` to `η_M(V)(m) ⊗_S η_N(V)(n)`. The proof rewrites
using the preceding adjunction characterization and then reduces the
sectionwise tensor operations by definition.

`presheafPullbackTensorComparisonApp_eq` expresses the comparison as `L`
applied to the defining composite, followed by `ε` at `L(M) ⊗ L(N)`.
This is Mathlib's `Adjunction.homEquiv_counit`.

For `a : M ⟶ M'` and `b : N ⟶ N'`,
`presheafPullbackTensorComparisonApp_naturality` proves

```
L.map (a ⊗ₘ b) ≫ presheafPullbackTensorComparisonApp f M' N' =
  presheafPullbackTensorComparisonApp f M N ≫ (L.map a ⊗ₘ L.map b).
```

The proof applies injectivity of the adjunction bijection, its two
naturality laws, naturality of the pushforward comparison, functoriality
of tensor on morphisms, and naturality of `η`.
`presheafPullbackTensorComparison f` packages the components as the
natural transformation from
`MonoidalCategory.tensor Y.PresheafOfModules ⋙ L` to
`L.prod L ⋙ MonoidalCategory.tensor X.PresheafOfModules`.
`presheafPullbackTensorComparison_app` identifies its components by definition.

## Provenance and scope

This is internal derived presheaf infrastructure, modeled on the published
sheaf comparison in `Langlands.AlgebraicGeometry.Modules.PullbackTensor`.
That imported module is unchanged. The construction here uses the pinned
Mathlib APIs in `Algebra/Category/ModuleCat/Presheaf/Pushforward.lean`,
`Pullback.lean`, and `Monoidal.lean`, and the adjunction API, at Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`, environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

The motivating sheaf result is the Stacks Project, Lemma 17.16.4,
[tag 01CD](https://stacks.math.columbia.edu/tag/01CD), in Section 17.16
(tag 01CA). It states functorial compatibility of sheaf-module pullback
with tensor products and omits its proof. The registered source is
`stacks-module-tensor-products-2026-10-21`, *Stacks Project - Tensor
products of sheaves of modules (HTML snapshot 2026-10-21)*, with SHA256
`825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`.
The present presheaf construction and its implemented proofs are derived
content, not a claim that the Stacks lemma itself states these presheaf
maps or proves their invertibility. The later presheaf invertibility and
transport through sheafification remain separate obligations.

Worker 5 implemented the construction and proofs. Worker 150 supplied the
downstream adjunction-image formula and its explicit scalar-argument
presentation, used here to expose the required interface.
