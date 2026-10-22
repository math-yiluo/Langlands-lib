# The canonical tensor comparison for pullback of module sheaves

For every morphism of schemes `f : X ⟶ Y` in universe `u`, this module
constructs the canonical natural transformation

```
pullbackTensorComparison f :
  tensorFunctor Y ⋙ AlgebraicGeometry.Scheme.Modules.pullback f ⟶
    (Scheme.Modules.pullback f).prod (Scheme.Modules.pullback f) ⋙ tensorFunctor X
```

Its component at `(M, N)` is the canonical map
`f^*(M ⊗ N) → f^*M ⊗ f^*N` of sheaves of `𝒪_X`-modules. All declarations are in
the namespace `Langlands.Scheme.Modules`. The tensor product is the explicit
bifunctor `tensorFunctor` from the published module
`Langlands.AlgebraicGeometry.Modules.Tensor`, which this module does not change.
Pullback, pushforward and their adjunction are Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback f`, `Scheme.Modules.pushforward f`
and `Scheme.Modules.pullbackPushforwardAdjunction f`. The module assumes no
monoidal structure on `X.Modules` and no monoidal or tensor-preservation
instance for pullback. It does not prove that the comparison is invertible.

Throughout, `f⁻¹U` denotes `(TopologicalSpace.Opens.map f.base).op.obj U` for
an open `U` of `Y`, and `η` denotes the unit of the sheafification adjunction
`sheafifyAdjunction X`.

## The pushforward tensor map

`restrictScalarsTensorLift φ g` is a small module-level helper. Take a ring
homomorphism `φ : R →+* S` of commutative rings, `S`-modules `M`, `N` and `T`,
and an `S`-linear map `g : M ⊗_S N → T`. The helper is the `R`-linear map
`M ⊗_R N → T` sending `m ⊗ n` to `g (m ⊗ n)`. Here `R` acts on `M`, `N` and
`T` by restriction of scalars along `φ`. It is built with Mathlib's
`ModuleCat.MonoidalCategory.tensorLift`, and well-definedness is the
`R`-bilinearity of `(m, n) ↦ g (m ⊗_S n)`. `restrictScalarsTensorLift_tmul`
records the formula, which holds by definition.

`tensorSheafifyUnit P Q` is the component of `η` at the sectionwise tensor
presheaf `P.val ⊗ Q.val`, for `P Q : X.Modules`. It is a morphism of presheaves
of modules `P.val ⊗ Q.val ⟶ (tensorObj P Q).val`, and sends a sectionwise
`p ⊗ q` to its image in the sheaf tensor product.

`pushforwardTensorPresheafHom f P Q` is a morphism of presheaves of
`𝒪_Y`-modules

```
(f_*P).val ⊗ (f_*Q).val ⟶ (f_*(tensorObj P Q)).val,
```

where `f_*` is `Scheme.Modules.pushforward f`. Over an open `U` of `Y`, the
sections of `f_*P` are `P(f⁻¹U)`, and `𝒪_Y(U)` acts through the structure-sheaf
map `f.c.app U : 𝒪_Y(U) → 𝒪_X(f⁻¹U)` of `f`. The component at `U` is
`restrictScalarsTensorLift (f.c.app U).hom` applied to the component of
`tensorSheafifyUnit P Q` at `f⁻¹U`. This construction uses no other scalar
restriction. `pushforwardTensorPresheafHom_app_tmul` states the resulting
formula, which holds by definition: for `p ∈ P(f⁻¹U)` and `q ∈ Q(f⁻¹U)`, the
element `p ⊗ q` maps to `η_{f⁻¹U}(p ⊗ q)`. Naturality in `U` follows from the
naturality of `η`, checked on pure tensors.

`pushforwardTensorApp f P Q : tensorObj (f_*P) (f_*Q) ⟶ f_*(tensorObj P Q)` is
the sheaf morphism that the bijection `tensorHomEquiv` (the sheafification
adjunction on `Y`) sends to `pushforwardTensorPresheafHom f P Q`. The lemma
`tensorHomEquiv_pushforwardTensorApp` states this correspondence, and
`pushforwardTensorApp_naturality` states naturality in both factors.
They are packaged as the natural transformation

```
pushforwardTensor f :
  (Scheme.Modules.pushforward f).prod (Scheme.Modules.pushforward f) ⋙ tensorFunctor Y ⟶
    tensorFunctor X ⋙ Scheme.Modules.pushforward f
```

whose component at `(P, Q)` is `pushforwardTensorApp f P Q`
(`pushforwardTensor_app`, by definition).

## The pullback tensor comparison

Write `η'` for the unit of `pullbackPushforwardAdjunction f`.
`pullbackTensorComparisonApp f M N : f^*(tensorObj M N) ⟶ tensorObj (f^*M) (f^*N)`
corresponds, under the adjunction bijection
`(pullbackPushforwardAdjunction f).homEquiv`, to the composite

```
tensorObj M N --tensorMap (η'_M) (η'_N)--> tensorObj (f_*f^*M) (f_*f^*N)
  --pushforwardTensorApp f (f^*M) (f^*N)--> f_*(tensorObj (f^*M) (f^*N)).
```

`homEquiv_pullbackTensorComparisonApp` states this correspondence.
`pullbackTensorComparisonApp_eq` gives the explicit form: `f^*` applied to this
composite, followed by the counit of the adjunction at
`tensorObj (f^*M) (f^*N)`. `pullbackTensorComparisonApp_naturality` states
naturality in `M` and `N`. The proof transports the equation through the
adjunction bijection and uses naturality of `η'`, naturality of
`pushforwardTensorApp`, and the composition law of `tensorMap`.

`pullbackTensorComparison f` packages these components as the natural
transformation shown at the top. Its component at `(M, N)` is
`pullbackTensorComparisonApp f M N` (`pullbackTensorComparison_app`, by
definition). This is the construction prescribed by the task, with no
alternative construction substituted.

## Auxiliary lemmas and instance

These lemmas are categorical consequences of the sheafification adjunction
and the functoriality of `tensorFunctor`:

- `tensorHomEquiv_tensorMap_comp`: under `tensorHomEquiv`, precomposing with
  `tensorMap a b` corresponds to precomposing with the presheaf tensor
  `a.val ⊗ₘ b.val`.
- `tensorHomEquiv_comp`: postcomposing with a sheaf morphism `h` corresponds to
  postcomposing with `h.val`.
- `tensorSheafifyUnit_naturality`: naturality of `η` with respect to
  `tensorMap`.
- `tensorMap_comp`: `tensorMap a b ≫ tensorMap a' b' = tensorMap (a ≫ a') (b ≫ b')`.

A local instance repeats the one in `Tensor.lean`. It exposes Mathlib's
monoidal structure on `PresheafOfModulesOfCommRing.{u} X.presheaf` through the
definitionally equal category `X.PresheafOfModules`. It is local, imposes no
hypotheses, and installs no monoidal instance on `X.Modules`.

## Source and provenance

The original source is the Stacks Project, Section 17.16 (tag 01CA), and
Lemma 17.16.4 (tag 01CD) in that section. The opening of Section 17.16 defines
`ℱ ⊗_{𝒪_X} 𝒢` as the sheafification of
`U ↦ ℱ(U) ⊗_{𝒪_X(U)} 𝒢(U)`, which `Tensor.lean` implements. Lemma 17.16.4
states that for a morphism of ringed spaces `f : (X, 𝒪_X) → (Y, 𝒪_Y)` and
`𝒪_Y`-modules `ℱ`, `𝒢`, we have
`f^*(ℱ ⊗_{𝒪_Y} 𝒢) = f^*ℱ ⊗_{𝒪_X} f^*𝒢`, functorially in `ℱ` and `𝒢`. The
source omits the proof.

This module specializes to morphisms of schemes. It constructs the canonical,
natural morphism `f^*(ℱ ⊗ 𝒢) → f^*ℱ ⊗ f^*𝒢` underlying that identification,
by the usual adjunction argument described above. It does **not** prove that
this morphism is an isomorphism. Invertibility and monoidal coherence (unit,
associativity and symmetry compatibilities) remain separate obligations of the
parent task `85c37e67-6dd6-478e-bf85-a199cd8ba222`.

The source is registered as `stacks-module-tensor-products-2026-10-21`,
*Stacks Project - Tensor products of sheaves of modules (HTML snapshot
2026-10-21)*. The retained HTML file has SHA256
`825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`.

The helper `restrictScalarsTensorLift`, the auxiliary lemmas and the local
instance are internal packaging needed for this construction. They are
derived from Mathlib's `ModuleCat.MonoidalCategory.tensorLift`, the adjunction
API, and the published `Tensor.lean` interface. The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
