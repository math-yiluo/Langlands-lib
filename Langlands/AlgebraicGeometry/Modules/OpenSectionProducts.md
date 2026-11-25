# Sections of finite products of module sheaves over opens

Let `X` be a scheme, `ι : Type` a finite index type and `N : ι → X.Modules` a
family of module sheaves.

- `piSectionsIso N V` identifies the sections over an open `V` of the product
  `∏ᶜ N` with the product module `∀ j, Γ(N j, V)`. It composes the product
  comparison of `SheafOfModules.evaluation` at `V`, which preserves limits, with
  Mathlib's `ModuleCat.piIsoPi`. `piSectionsIso_hom_apply` states that the
  `j`-th component is the section map of the projection `Pi.π N j`.
- `bijective_app_of_isIso_pullback` covers a morphism `φ : M ⟶ N` whose
  pullback along the inclusion `W.ι` of an open `W` is an isomorphism. It states
  that `φ.app V` is bijective for every open `V ≤ W`. The proof transports the
  isomorphism along Mathlib's `restrictFunctorIsoPullback`. Sections of the
  restriction over `V'` are the sections over the image `W.ι ''ᵁ V'`, and
  `V = W.ι ''ᵁ (W.ι ⁻¹ᵁ V)` because `V ≤ W`.
- `bijective_pi_app_of_isIso_pullback` covers a finite family
  `f j : M ⟶ N j` whose product morphism `Pi.lift f` becomes an isomorphism
  after pullback to `W`. It states that the joint evaluation
  `s ↦ (j ↦ (f j).app V s)` is bijective on sections over every open
  `V ≤ W`.

## Provenance

These are internal lemmas about Mathlib's sheaves of modules. They are used in
the torsion bracket part of the eventual quasi-projectivity of fine moduli
schemes of ordinary polarized full-level data (module
`Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionBracketMapReduction`) to
turn membership in the projective frame locus, defined as a supremum of opens on which the joint
torsion evaluation becomes an isomorphism after pullback, into bijectivity of
joint evaluation on sections over smaller opens.
