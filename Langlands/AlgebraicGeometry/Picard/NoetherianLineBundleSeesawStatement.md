# The noetherian seesaw for line bundles on a flat proper family

`Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawStatement.{u}` is the
proposition:

```lean
∀ {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
  [IsProper c] [Flat c] [GeometricallyIntegral c],
  (∀ (B : Type u) [CommRing B] [Algebra R B],
    Function.Bijective
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop) →
  ∀ {T : Scheme.{u}} [IsLocallyNoetherian T] (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : (pullback c t).Modules),
    IsLocallyFreeRankOne M → IsLocallyFreeRankOne M' →
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ T), IsClosedImmersion ι ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T),
        (∃ z : T' ⟶ Z, z ≫ ι = ψ) ↔
          ∀ τ : T', ∃ U : T'.Opens, τ ∈ U ∧
            Nonempty
              (((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) ψ)).obj M).restrict
                  (pullback.snd (pullback.snd c t) ψ ⁻¹ᵁ U).ι ≅
                ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) ψ)).obj M').restrict
                  (pullback.snd (pullback.snd c t) ψ ⁻¹ᵁ U).ι)
```

This unit only defines the proposition. It proves nothing.

## Meaning

Let `R` be a commutative ring and `c : X ⟶ Spec R` a proper, flat morphism whose geometric
fibres are integral. Assume that taking global functions commutes with every affine base
change: for each `R`-algebra `B`, the map on global sections induced by the projection
`X ×_{Spec R} Spec B ⟶ Spec B` is bijective. Let `T` be a locally noetherian scheme with a
morphism `t : T ⟶ Spec R`, and let `M`, `M'` be two line bundles on `X_T = X ×_{Spec R} T`.

Then there is a closed immersion `ι : Z ⟶ T` with the following property. For any scheme
`T'` and any morphism `ψ : T' ⟶ T`, write `p : X_T ×_T T' ⟶ T'` for the second projection
and pull `M` and `M'` back along the first projection `X_T ×_T T' ⟶ X_T`. Then `ψ` factors
through `ι` exactly when every point `τ` of `T'` has an open neighbourhood `U` such that the
two pullbacks become isomorphic on `p⁻¹(U)`.

So `Z` represents the subfunctor of `T` on which `M` and `M'` agree locally on the base. This
is a form of the seesaw principle. The source phrases the condition differently, through an
invertible sheaf on `T'`; see Provenance.

## Exact interface

- `pullback c t` is Mathlib's chosen fibre product `X ×_{Spec R} T`, and
  `pullback.snd c t : X_T ⟶ T` is its structure morphism over `T`. The family over `T'` is
  the chosen fibre product `pullback (pullback.snd c t) ψ`, with projections
  `pullback.fst … ψ` to `X_T` and `pullback.snd … ψ` to `T'`.
- `IsLocallyFreeRankOne` is the published Library predicate from
  `Langlands.AlgebraicGeometry.Picard.LineBundle`: every point has an open neighbourhood `V`
  with `M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf`.
- `Scheme.Modules.pullback` and `Scheme.Modules.restrict` are Mathlib's pullback of sheaves of
  modules and restriction along an open immersion. Local agreement is stated on the open
  subscheme `p⁻¹(U)` through restriction along its inclusion `(p ⁻¹ᵁ U).ι`.
- `IsProper`, `Flat`, `GeometricallyIntegral`, `IsLocallyNoetherian`, `IsClosedImmersion` and
  `Scheme.Hom.appTop` are Mathlib's.
- The hypothesis on global functions is stated only for affine base changes
  `Spec.map (CommRingCat.ofHom (algebraMap R B))`, not for all base changes.

The test schemes `T'` are arbitrary; only `T` is assumed locally noetherian. `R`, `X`, `T`,
`T'` and `Z` all lie in universe `u`. Nothing is defined here except the proposition itself.

## Provenance

Derived. The mathematics is the Stacks Project, *More on Morphisms*, Section 37.33 "Theorem
of the cube", Lemma 37.33.1 (tag 0BDP, label `lemma-diagonal-picard-flat-proper`) together
with Lemma 37.33.4 (tag 0BF0, label `lemma-get-a-closed`); registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, file `more-morphisms.tex`. Lemma 0BDP gives an
immersion `Z ⟶ S` of finite presentation through which `g : T ⟶ S` factors exactly when
`q^*E ≅ p^*N` for a finite locally free `N` on `T`, assuming `𝒪_T → p_*𝒪_{X_T}` is an
isomorphism for all `T`. Lemma 0BF0 says `Z` is closed when `E` is invertible and the
geometric fibres are integral.

The present proposition applies those lemmas to the family `X_T ⟶ T` and to `E = M ⊗ M'⁻¹`,
and states the conclusion as local isomorphism of `M` and `M'` over the base instead of
through `E` and `N`. The setting differs from the source as follows:

- the base `S` of the source is the locally noetherian scheme `T`, and the family over it is
  the base change of a family over an affine scheme `Spec R`; this narrows the scope;
- the geometric-fibre condition is Mathlib's `GeometricallyIntegral c` on the family over
  `Spec R`;
- the condition on `𝒪_T → p_*𝒪_{X_T}` is asked only on global sections and only for affine
  base changes `Spec B ⟶ Spec R` of `c`. Every scheme over `Spec R` is covered by affine
  opens of this form, which is how this matches the source's condition, but that comparison
  is not part of this unit;
- finite presentation of `X_T ⟶ T` is not assumed separately: `c` is proper, so `X_T ⟶ T`
  is of finite type over the locally noetherian `T`.

The statement is the Library-language transcription of the theorem
`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper`
of the Anthropic Lean source of Fermat's Last Theorem (registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, file
`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper.lean`).
All binders, hypotheses and the conclusion are the same, with two changes of language:

- that source's `Scheme.Modules.IsInvertible M` asks for local trivialisations
  `(Scheme.Modules.pullback V.ι).obj M ≅ unit`; here the Library predicate
  `IsLocallyFreeRankOne M` uses `M.restrict V.ι` instead;
- that source's `Scheme.Modules.LocallyIsoOver p N N'` asks for isomorphisms
  `(Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj N ≅ (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj N'`;
  here it is written out with `restrict` along `(p ⁻¹ᵁ U).ι`.

For an open immersion, Mathlib's `Scheme.Modules.restrictFunctorIsoPullback` identifies
restriction with pullback, so the two formulations agree. This unit does not prove that
agreement.

The proposition is introduced as the cohomological input for the noetherian affine case
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedNoetherianAffineStatement` (task
`00ab6acd-8b6c-4595-8df8-3fbdac0bdd4d`), applied there with `c` the structure morphism of an
abelian scheme over `Spec R`.
