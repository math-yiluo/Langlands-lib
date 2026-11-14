# Pasting base change transformations

Author: Worker 26. Builds on the following modules:

- `Langlands.Cohomology.ExactBaseChange`: the base change transformation
  `baseChangeNatTrans τ n : F₁.rightDerived n ⋙ β ⟶ α ⋙ F₂.rightDerived n` of a natural
  transformation `τ : F₁ ⋙ β ⟶ α ⋙ F₂`.
- `Langlands.Cohomology.ExactBaseChange.ResolutionMap` and
  `Langlands.Cohomology.ExactBaseChange.ResolutionProof` (Worker 1245):
  `resolutionBaseChangeMap τ ψ`, `quasiIso_mapResolutionAugmentation`, and the comparison
  equality `resolutionComparison_baseChangeNatTrans`, which computes
  `β.map (resolutionComparison F₁ ε n) ≫ (baseChangeNatTrans τ n).app A` from any right
  resolutions `ε` of `A` and `ε'` of `α A` and a cochain map `ψ` with
  `mapResolutionAugmentation α ε ≫ ψ = ε'`.
- `Langlands.Cohomology.AcyclicResolution.Lift` and
  `Langlands.Cohomology.AcyclicResolution.Comparison` (through the imports), namespace
  `Langlands.Cohomology.AcyclicResolution`: `lift`, `comp_lift_id`, `comparison`,
  `resolutionComparison` and `resolutionComparison_eq`.
- `Langlands.Cohomology.LeftExactHomology` (through the imports): for an additive functor
  `Φ` that preserves finite limits, `toCycles Φ S`, `homologyHom Φ S : H(Φ S) ⟶ Φ (H S)` and
  `homologyNatTrans Φ c i`.

This module contains no geometry. It is a helper for
`Langlands.Sheaf.Equivariant.TwistedRepComparison` (this candidate).

## Purpose

Consider two squares of additive functors

```
C₁ --F₁--> D₁        C₂ --F₂--> D₂
|α         |β        |δ         |γ
C₂ --F₂--> D₂        C₃ --F₃--> D₃
```

with natural transformations `τ₀ : F₁ ⋙ β ⟶ α ⋙ F₂` and `τ₂ : F₂ ⋙ γ ⟶ δ ⋙ F₃`. If the
vertical functors are exact, the base change transformation of the stacked square
`C₁ → C₃`, `D₁ → D₃` is the composite of the base change transformations of the two squares.
`TwistedRepComparison` uses this to factor a comparison map of cohomology modules through a
morphism of representations.

## Declarations in `Langlands.Cohomology.LeftExactHomology`

Let `D`, `E`, `E'` be abelian categories and `β : D ⥤ E`, `γ : E ⥤ E'` additive functors
that preserve finite limits.

- `toCycles_comp β γ S`: for a short complex `S` in `D`,
  `toCycles (β ⋙ γ) S = γ.map (toCycles β S) ≫ toCycles γ (S.map β)`. This holds for any
  additive `β`, `γ`. Proof: both sides agree after composing with the monomorphism
  `iCycles`, by `toCycles_iCycles` (three times) and functoriality of `γ`.
- `homologyHom_comp β γ S`:
  `homologyHom (β ⋙ γ) S = homologyHom γ (S.map β) ≫ γ.map (homologyHom β S)`. Proof: both
  sides agree after precomposing with the epimorphism `toCycles (β ⋙ γ) S ≫ homologyπ`. The
  proof uses `toCycles_comp` and `toCycles_homologyπ_homologyHom` (three times).
- `homologyNatTrans_comp_app β γ c i K`: the same identity for the components of
  `homologyNatTrans` at a homological complex `K`. It is `homologyHom_comp` at `K.sc i`.

## Declarations in `Langlands.Cohomology.ExactBaseChange`

For any categories and functors `F₁ : C₁ ⥤ D₁`, `F₂ : C₂ ⥤ D₂`, `F₃ : C₃ ⥤ D₃`,
`α : C₁ ⥤ C₂`, `δ : C₂ ⥤ C₃`, `β : D₁ ⥤ D₂`, `γ : D₂ ⥤ D₃`:

- `pasteNatTrans τ₀ τ₂ : F₁ ⋙ β ⋙ γ ⟶ (α ⋙ δ) ⋙ F₃` (with `@[simps]`), for
  `τ₀ : F₁ ⋙ β ⟶ α ⋙ F₂` and `τ₂ : F₂ ⋙ γ ⟶ δ ⋙ F₃`. Its component at `A` is
  `γ.map (τ₀.app A) ≫ τ₂.app (α.obj A)`. Naturality follows from that of `τ₀` and `τ₂`.

Now let all six categories be abelian, and let `C₁`, `C₂`, `C₃` have injective resolutions.
Let `F₁`, `F₂`, `F₃` be additive, and let `α`, `δ`, `β`, `γ` be additive, preserve finite
limits and preserve homology.

- `isIso_resolutionComparison_injectiveResolution A n`: for Mathlib's chosen injective
  resolution `injectiveResolution A`, `resolutionComparison F₁ (injectiveResolution A).ι n` is
  an isomorphism. This needs only `F₁` additive and `C₁` abelian with injective resolutions.
  Proof: by `resolutionComparison_eq` with the identity of the resolution, it is the image of
  the identity under `comparison`, hence an isomorphism.
- `baseChangeNatTrans_paste_app τ₀ τ₂ n A`: assuming also that `β ⋙ γ` and `α ⋙ δ`
  preserve homology,
  `(baseChangeNatTrans (pasteNatTrans τ₀ τ₂) n).app A =
  γ.map ((baseChangeNatTrans τ₀ n).app A) ≫ (baseChangeNatTrans τ₂ n).app (α.obj A)`.

  Proof. Let `I` and `J` be the chosen injective resolutions of `A` and `α A`, and
  `K = I.cocomplex`. The cochain map `ψ₀ : α K ⟶ J.cocomplex` is the lift of `J.ι` along the
  resolution `α I.ι` (`lift`, `comp_lift_id`). Then `ψ₁ = δ ψ₀` satisfies
  `mapResolutionAugmentation (α ⋙ δ) I.ι ≫ ψ₁ = mapResolutionAugmentation δ J.ι`. The
  comparison equality `resolutionComparison_baseChangeNatTrans` gives three identities:

  - for `τ₀`, with `ε = I.ι`, `ε' = J.ι`, `ψ = ψ₀`;
  - for `τ₂`, with `ε = J.ι`, `ε' = δ J.ι`, `ψ = 𝟙`;
  - for the pasted transformation, with `ε = I.ι`, `ε' = δ J.ι`, `ψ = ψ₁`.

  Both sides of the claim are cancelled against the isomorphism
  `(β ⋙ γ).map (resolutionComparison F₁ I.ι n)`. The two sides then agree by the
  following facts:

  - `γ` applied to `resolutionBaseChangeMap τ₀ ψ₀`, followed by
    `resolutionBaseChangeMap τ₂ 𝟙`, is `resolutionBaseChangeMap (pasteNatTrans τ₀ τ₂) ψ₁`.
    This follows componentwise from the naturality of `τ₂`.
  - `homologyNatTrans γ` is natural.
  - `homologyNatTrans_comp_app`. It gives the inverse of `homologyNatTrans (β ⋙ γ)` as the
    composite of the inverses, via `IsIso.inv_eq_of_hom_inv_id`.

## Provenance

This module is our own homological algebra. It is internal infrastructure and makes no
claim from the literature. The statement is the usual compatibility of the base change
morphism of derived functors with pasting of squares.
