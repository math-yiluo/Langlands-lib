# Open restriction commutes with the sheaf tensor product: proof

This module proves the published proposition
`Langlands.Scheme.Modules.RestrictTensorComparisonStatement` from
`Langlands.AlgebraicGeometry.Modules.RestrictTensorStatement`, which it imports
unchanged. It also imports Mathlib's
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization`.

## Main result

`Langlands.Scheme.Modules.restrictTensorComparison` is the theorem

```lean
theorem restrictTensorComparison (X : Scheme.{u}) : RestrictTensorComparisonStatement X
```

for an arbitrary scheme `X` and an arbitrary universe `u`, with no further
hypotheses. For every open `U : X.Opens` and all `M N : X.Modules` it gives the
two clauses of the statement:

1. `IsIso (restrictTensorHom U M N)`, from the lemma `isIso_restrictTensorHom`;
2. the value of the comparison at an open `V : U.toScheme.Opens` on the
   sheafified pure tensor `m ⊗ₜ n` of sections over `V` (tensor over
   `U.toScheme.presheaf.obj (op V)`) is the sheafified pure tensor `m ⊗ₜ n`
   over `U.ι ''ᵁ V` (tensor over `X.presheaf.obj (op (U.ι ''ᵁ V))`). This is
   the lemma `restrictTensorHom_app_tmul`.

The comparison `restrictTensorHom` and its parts `restrictRingMap`,
`restrictTensorLift` and `restrictTensorPresheafHom` are the published
definitions in `Langlands.AlgebraicGeometry.Modules.RestrictTensor`.
`restrictTensorHom U M N` is the transpose, under the published
`tensorHomEquiv`, of the presheaf map

```text
restrictTensorPresheafHom U M N =
  restrictTensorLift U M N ≫ pushforward(restrictRingMap U).map (tensorSheafifyUnit M N).
```

## Algebraic lemma

`restrictScalarsTensorLift_id_bijective`: for a surjective ring map
`φ : R →+* S` of commutative rings and `S`-modules `M`, `N`, the canonical
`R`-linear map

```text
restrictScalarsTensorLift φ (𝟙 (M ⊗ N)) : M ⊗[R] N ⟶ M ⊗[S] N,  m ⊗ n ↦ m ⊗ n
```

is bijective. Here `M ⊗[R] N` is the tensor product of the restrictions of
scalars of `M` and `N` along `φ`. Surjectivity is proved by induction on
tensors. For injectivity, the proof builds an additive map
`g : M ⊗[S] N →+ M ⊗[R] N` with `TensorProduct.liftAddHom`, sending `m ⊗ n`
to `m ⊗ n`. Its `S`-balancedness `f (s • m) n = f m (s • n)` holds because
every `s` is `φ r` for some `r`, and the `R`-tensor product is `R`-balanced.
Induction on tensors shows that `g` is a left inverse of the canonical map.

## Invertibility

1. `isIso_sheafify_map_of_W`: for a presheaf of modules map `f : P ⟶ Q` on a
   scheme `Y`, if the underlying map of abelian presheaves lies in
   `(Opens.grothendieckTopology Y).W`, then `(sheafify Y).map f` is an
   isomorphism. The proof is Mathlib's
   `PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`,
   applied to the identity map of the structure ring sheaf (the published
   `sheafify Y` is module sheafification along that identity).
2. `restrictTensorLift_app_bijective`: each component
   `(restrictTensorLift U M N).app V` is bijective. It is the algebraic lemma
   for the ring map `(U.ι.appIso V).inv`, which is surjective because
   `(U.ι.appIso V).hom` gives preimages.
3. `isIso_sheafify_map_restrictTensorLift`: a sectionwise injective
   (surjective) map is locally injective (locally surjective), by Mathlib's
   `Presheaf.isLocallyInjective_of_injective` and
   `Presheaf.isLocallySurjective_of_surjective`. Mathlib's
   `GrothendieckTopology.W_of_isLocallyBijective` puts the map in `W`, and
   step 1 shows that `(sheafify U).map (restrictTensorLift U M N)` is an
   isomorphism.
4. `isIso_sheafify_map_pushforward_tensorSheafifyUnit`: after forgetting to
   abelian presheaves, the pushforward of `tensorSheafifyUnit M N` along
   `restrictRingMap U` is, by definition, the whiskering along
   `U.ι.opensFunctor.op` of Mathlib's abelian sheafification map
   `toSheafify (Opens.grothendieckTopology X) (M.val ⊗ N.val).presheaf`. The
   proof states this with `change`. Mathlib's
   `Presheaf.isLocallyInjective_whisker` and
   `Presheaf.isLocallySurjective_whisker` show that this whiskering is locally
   injective and locally surjective. They use Mathlib's instances that
   `U.ι.opensFunctor` is cocontinuous and that `toSheafify` is locally
   injective and locally surjective. Then `W_of_isLocallyBijective` and step 1
   apply again.
5. `restrictTensorHom_eq`: by the counit form of the adjunction's hom
   equivalence (`Adjunction.homEquiv_counit`) and `Functor.map_comp`,

   ```text
   restrictTensorHom U M N =
     (sheafify U).map (restrictTensorLift U M N) ≫
       (sheafify U).map (pushforward(restrictRingMap U).map (tensorSheafifyUnit M N)) ≫
       (sheafifyAdjunction U).counit.app ((tensorObj M N).restrict U.ι).
   ```

   The proof writes the composition and reassociation as an explicit term
   (`congrArg`, `Functor.map_comp`, `Category.assoc`), not with `rw`.
6. `isIso_restrictTensorHom`: the counit of the sheafification adjunction at
   the sheaf `(tensorObj M N).restrict U.ι` is an isomorphism by an existing
   instance. With steps 3 and 4, the composite in step 5 is a composite of
   three isomorphisms. The proof passes these three facts explicitly to
   `IsIso.comp_isIso` and transports along the equation of step 5. It is a
   lemma, not an instance.

## Values on pure tensors

- `tensorSheafifyUnit_comp_tensorHomEquiv_symm`: for module sheaves `P Q T` on
  any scheme and a presheaf map `f : P.val ⊗ Q.val ⟶ T.val`,
  `tensorSheafifyUnit P Q ≫ ((tensorHomEquiv P Q T).symm f).val = f`. This is
  the unit form of the adjunction's hom equivalence
  (`Adjunction.homEquiv_unit`) combined with `Equiv.apply_symm_apply`.
- `tensorSheafifyUnit_comp_restrictTensorHom` specializes this to
  `restrictTensorHom`: precomposing it with the unit gives
  `restrictTensorPresheafHom U M N`.
- `restrictTensorHom_app_tmul` evaluates that equation at `op V` on
  `m ⊗ₜ n`. By definition, `restrictTensorPresheafHom` sends the pure tensor
  over `U.toScheme.presheaf.obj (op V)` to the image under
  `(tensorSheafifyUnit M N).app (op (U.ι ''ᵁ V))` of the pure tensor over
  `X.presheaf.obj (op (U.ι ''ᵁ V))`, so the equation closes by definitional
  unfolding. This is clause 2 of the statement.

## Provenance

The statement is the open-immersion case of
[Stacks Project, Lemma 17.16.4 (tag 01CD)](https://stacks.math.columbia.edu/tag/01CD),
for the tensor product of Section 17.16 (tag 01CA). The retained source is
`stacks-module-tensor-products-2026-10-21` (SHA-256
`825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`). The
source omits the proof of Lemma 17.16.4, so the route above is internal. It
proves the open-immersion case directly for `restrictTensorHom`, and neither
uses nor states the general pullback/tensor comparison
`pullbackTensorComparisonApp`.

Worker 207 wrote the original draft of this proof. Worker 870 adapted it to
the published definitions and statement, removed the local elaboration option
`backward.isDefEq.respectTransparency false` that the draft used in steps 5
and 6, and revised this Markdown.

## Scope

All lemmas in the module are public, in namespace `Langlands.Scheme.Modules`.
No naturality of the comparison in `M` and `N` is proved. No compatibility
with associators, unitors or the localized monoidal structure `⊗` on
`X.Modules` is proved either.
