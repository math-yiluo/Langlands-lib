# Limits and colimits under normalized parabolic induction and restriction

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviParabolicFunctorsPreserveLimitsStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviParabolicFunctorsPreserveLimitsStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.1.2, Corollary, printed p.136 / PDF p.142. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Corollary says: the functor `i_P^G` preserves limits; adapting the remark of the previous paragraph, one sees easily that it also preserves colimits; the functor `r_P^G` preserves colimits. Here `P = MN` is a parabolic subgroup of `G`, and `i_P^G`, `r_P^G` are the normalized functors (VI.1.2.1) and (VI.1.2.2) of the same page.

This is a **derived** formulation, because the functors are the published normalized functors of the represented-parabolic interface, transported to representations of `M(F)`, and "limits" and "colimits" are read as small limits and colimits in the sense of Mathlib (see "Size of the diagrams").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`, every rational Levi `l : M ⟶ P` with `hl : IsRationalLeviSubgroup l`, and every matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`.

For these data it installs on `rationalPoints M` the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl` from the published Levi-point interface `ArbitraryParabolicLeviPoints`. It then asserts the conjunction of

1. `Limits.PreservesLimitsOfSize.{v, v} (leviInductionFunctor.{u, v} p l r hp hr hl hmul)`;
2. `Limits.PreservesColimitsOfSize.{v, v} (leviInductionFunctor.{u, v} p l r hp hr hl hmul)`;
3. `Limits.PreservesColimitsOfSize.{v, v} (leviJacquetFunctor.{u, v} p l r hp hr hl hmul)`.

## The objects

- `leviInductionFunctor p l r hp hr hl hmul : SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` is the published normalized parabolic induction `i_P^G`. It pulls back along the inverse of `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)` and applies the published `inductionFunctor` from the Levi image.
- `leviJacquetFunctor p l r hp hr hl hmul : SmoothRep.{0, u, v} ℂ (rationalPoints G) ⥤ SmoothRep.{0, u, v} ℂ (rationalPoints M)` is the published normalized Jacquet functor `r_P^G`. It takes coinvariants for the radical image with the twisted action of the Levi image, then pulls back along `leviPointsEquiv p l hp hl`.
- Both twists use the usual Haar modulus. Renard's `δ_P` is its inverse (remark after (VI.1.2.2), printed p.136 / PDF p.142), so the published twists are Renard's `δ_P^{-1/2}` and `δ_P^{1/2}`.
- `SmoothRep.{0, u, v} ℂ X` is the published full subcategory of smooth objects in Mathlib's `Rep.{v} ℂ X`, the categories `M(G)` and `M(M)` of the source.

## Size of the diagrams

`Limits.PreservesLimitsOfSize.{v, v} F` says that `F` sends every limit cone of every diagram indexed by a category `J : Type v` with `[Category.{v} J]` to a limit cone, and similarly for colimits. The categories `SmoothRep.{0, u, v} ℂ _` are full subcategories of Mathlib's `Rep.{v} ℂ _`, whose morphisms are linear maps between carriers in `Type v`. So `J` ranges over the small index categories of the source categories, which is how the source's "limits" and "colimits" are read. No existence of limits or colimits is asserted.

The size is written explicitly. Mathlib's abbreviations `PreservesLimits F` and `PreservesColimits F` use the morphism universe of the target category of `F`. For `leviInductionFunctor` that universe is `max u v`, which would quantify over index categories larger than the small ones of the source category.

## Faithfulness notes

- The Corollary is stated for every parabolic `P = MN`. The statement quantifies over every actual rational parabolic with a rational Levi and a matching radical, not only standard ones.
- The induced representation has carrier universe `max u v`, as for the published induction functor. The Jacquet functor preserves the carrier universe `v`.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `M(F)` are derived from them, not assumed.

## Remaining obligations

The proof is a separate obligation. In the source, the first and third assertions follow from the adjunction of the Proposition of VI.1.2 (staged separately as `LeviFrobeniusReciprocityStatement`) through the properties of adjoint functors (A.V). The second follows from the remark after the Theorem of VI.1.1 (printed p.135 / PDF p.141). There, `G/P` is compact (Lemma III.2.3), so `Ind_P^G = ind_P^G`, and `ind_P^G` and the inflation functor have right adjoints. In Lean, the carrier universes of the two functors differ (`max u v` and `v`), so Mathlib's `Adjunction` does not directly apply. A proof must either work with the explicit bijection across universes or prove preservation directly. Preservation of colimits by `i_P^G` also needs compactness of `P\G`, the published `ArbitraryParabolicQuotientCompactStatement`, whose proof is task `c1ce4629-6768-4eb5-b4ee-0086526913ea`. None of this is asserted here.

## Provenance

This is a derived statement of the Corollary of VI.1.2 for the represented-parabolic interface. The functors are the published `leviInductionFunctor` and `leviJacquetFunctor`. Limits and colimits are Mathlib's small limits and colimits of the published smooth-representation categories.
