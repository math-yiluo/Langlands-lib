/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-!

# Affine charts of relative affine space and base change

Relative affine space `𝔸(n; S) = S ×_ℤ Spec ℤ[n]` is described locally on `S` by the charts
`Spec Γ(S, V)[n] ⟶ 𝔸(n; S)` for affine opens `V ⊆ S`. We record:

- each chart is an open immersion onto the preimage of `V`, exhibiting `Spec Γ(S, V)[n]` as
  the pullback of `𝔸(n; S)` along `Spec Γ(S, V) ⟶ S`, and the charts cover `𝔸(n; S)`;
- for affine opens `V' ⊆ V` the charts are compatible with the restriction maps
  `Γ(S, V)[n] → Γ(S, V')[n]`, and the transition maps satisfy the cocycle condition;
- for `g : T ⟶ S` there is a canonical isomorphism `𝔸(n; S) ×_S T ≅ 𝔸(n; T)` over `T`,
  compatible with the projections and with the charts.

## Main definitions

- `AlgebraicGeometry.AffineSpace.chart`: the chart `Spec Γ(S, V)[n] ⟶ 𝔸(n; S)`.
- `AlgebraicGeometry.AffineSpace.chartTransition`: the transition map between the charts of
  affine opens `V' ⊆ V`.
- `AlgebraicGeometry.AffineSpace.pullbackIso`: the base change isomorphism
  `𝔸(n; S) ×_S T ≅ 𝔸(n; T)`.

## Blueprint

This file implements `lemma-nagata-relative-affine-space-charts`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineSpace

variable (n : Type u) {S T : Scheme.{u}}

/-- The affine chart `Spec Γ(S, V)[n] ⟶ 𝔸(n; S)` of relative affine space over an affine
open `V` of `S`. (blueprint: `lemma-affine-covers-dense-intersection--2`) -/
noncomputable def chart {V : S.Opens} (hV : IsAffineOpen V) :
    Spec (.of (MvPolynomial n Γ(S, V))) ⟶ 𝔸(n; S) :=
  (SpecIso n Γ(S, V)).inv ≫ map n hV.fromSpec

instance {V : S.Opens} (hV : IsAffineOpen V) : IsOpenImmersion (chart n hV) := by
  unfold chart
  infer_instance

/-- The chart lies over `Spec Γ(S, V) ⟶ S`. -/
@[reassoc]
lemma chart_over {V : S.Opens} (hV : IsAffineOpen V) :
    chart n hV ≫ 𝔸(n; S) ↘ S =
      Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ hV.fromSpec := by
  rw [chart, Category.assoc, map_over, SpecIso_inv_over_assoc]

/-- The chart square is a pullback: `Spec Γ(S, V)[n]` is the base change of `𝔸(n; S)` along
`Spec Γ(S, V) ⟶ S`. -/
lemma isPullback_chart {V : S.Opens} (hV : IsAffineOpen V) :
    IsPullback (chart n hV) (Spec.map (CommRingCat.ofHom MvPolynomial.C))
      (𝔸(n; S) ↘ S) hV.fromSpec := by
  have h₁ : IsPullback (SpecIso n Γ(S, V)).inv (Spec.map (CommRingCat.ofHom MvPolynomial.C))
      (𝔸(n; Spec Γ(S, V)) ↘ Spec Γ(S, V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [SpecIso_inv_over, Category.comp_id]⟩
  have h := h₁.paste_horiz (isPullback_map (n := n) hV.fromSpec)
  rwa [Category.id_comp] at h

/-- The chart over `V` is an open immersion onto the preimage of `V`. -/
lemma opensRange_chart {V : S.Opens} (hV : IsAffineOpen V) :
    (chart n hV).opensRange = (𝔸(n; S) ↘ S) ⁻¹ᵁ V :=
  (isPullback_chart n hV).opensRange_fst.trans (by rw [hV.opensRange_fromSpec])

/-- The charts over the affine opens of `S` cover `𝔸(n; S)`. -/
lemma iSup_opensRange_chart :
    ⨆ V : S.affineOpens, (chart n V.2).opensRange = ⊤ := by
  simp_rw [opensRange_chart]
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top S, Scheme.Hom.preimage_top]

/-- The transition map `Spec Γ(S, V')[n] ⟶ Spec Γ(S, V)[n]` between the charts of affine
opens `V' ⊆ V`, induced by the restriction `Γ(S, V) → Γ(S, V')` on coefficients. -/
noncomputable def chartTransition {V V' : S.Opens} (h : V' ≤ V) :
    Spec (.of (MvPolynomial n Γ(S, V'))) ⟶ Spec (.of (MvPolynomial n Γ(S, V))) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (S.presheaf.map (homOfLE h).op).hom))

/-- Blueprint `lemma-affine-covers-dense-intersection--2`: Relative affine-space charts and
base change (compatibility of the charts).

For affine opens `V' ⊆ V` of `S`, the chart over `V'` is the chart over `V` precomposed with
the map induced by the restriction `Γ(S, V)[n] → Γ(S, V')[n]`. -/
@[reassoc]
lemma chartTransition_chart {V V' : S.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ V) :
    chartTransition n h ≫ chart n hV = chart n hV' := by
  rw [chartTransition, chart, chart, ← hV.map_fromSpec hV' (homOfLE h).op, map_comp,
    map_SpecMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Blueprint `lemma-affine-covers-dense-intersection--2`: Relative affine-space charts and
base change (cocycle condition).

For opens `V'' ⊆ V' ⊆ V` of `S` (affine in the application to charts), the transition
maps of the charts compose. -/
@[reassoc]
lemma chartTransition_comp {V V' V'' : S.Opens} (h' : V' ≤ V) (h'' : V'' ≤ V') :
    chartTransition n h'' ≫ chartTransition n h' = chartTransition n (h''.trans h') := by
  rw [chartTransition, chartTransition, chartTransition, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, MvPolynomial.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/-- The base change isomorphism `𝔸(n; S) ×_S T ≅ 𝔸(n; T)` for `g : T ⟶ S`.
(blueprint: `lemma-affine-covers-dense-intersection--2`) -/
noncomputable def pullbackIso (g : T ⟶ S) : pullback (𝔸(n; S) ↘ S) g ≅ 𝔸(n; T) :=
  (isPullback_map (n := n) g).isoPullback.symm

@[reassoc (attr := simp)]
lemma pullbackIso_hom_over (g : T ⟶ S) :
    (pullbackIso n g).hom ≫ 𝔸(n; T) ↘ T = pullback.snd _ _ :=
  (isPullback_map (n := n) g).isoPullback_inv_snd

@[reassoc (attr := simp)]
lemma pullbackIso_hom_map (g : T ⟶ S) :
    (pullbackIso n g).hom ≫ map n g = pullback.fst _ _ :=
  (isPullback_map (n := n) g).isoPullback_inv_fst

@[reassoc (attr := simp)]
lemma pullbackIso_inv_fst (g : T ⟶ S) :
    (pullbackIso n g).inv ≫ pullback.fst _ _ = map n g :=
  (isPullback_map (n := n) g).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma pullbackIso_inv_snd (g : T ⟶ S) :
    (pullbackIso n g).inv ≫ pullback.snd _ _ = 𝔸(n; T) ↘ T :=
  (isPullback_map (n := n) g).isoPullback_hom_snd

/-- Blueprint `lemma-affine-covers-dense-intersection--2`: Relative affine-space charts and
base change (base change of the charts).

For `g : T ⟶ S` and affine opens `W ⊆ T`, `V ⊆ S` with `W ⊆ g⁻¹ V`, the chart of `𝔸(n; T)`
over `W` followed by `𝔸(n; T) ⟶ 𝔸(n; S)` is the chart of `𝔸(n; S)` over `V` precomposed
with the map induced by `g^♯ : Γ(S, V) → Γ(T, W)` on coefficients. -/
@[reassoc]
lemma chart_map (g : T ⟶ S) {V : S.Opens} {W : T.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (e : W ≤ g ⁻¹ᵁ V) :
    chart n hW ≫ map n g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (g.appLE V W e).hom)) ≫ chart n hV := by
  rw [chart, chart, Category.assoc, ← map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec g hV hW e,
    map_comp, map_SpecMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Blueprint `lemma-affine-covers-dense-intersection--2`: Relative affine-space charts and
base change (the base change isomorphism is compatible with the charts).

Under `𝔸(n; S) ×_S T ≅ 𝔸(n; T)`, the chart of `𝔸(n; T)` over an affine open `W ⊆ g⁻¹ V`
maps to the pair consisting of the chart of `𝔸(n; S)` over `V` (after changing coefficients
along `g^♯`) and the structure map `Spec Γ(T, W)[n] ⟶ Spec Γ(T, W) ⟶ T`. -/
lemma chart_pullbackIso_inv (g : T ⟶ S) {V : S.Opens} {W : T.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (e : W ≤ g ⁻¹ᵁ V) :
    chart n hW ≫ (pullbackIso n g).inv ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (MvPolynomial.map (g.appLE V W e).hom)) ≫ chart n hV ∧
      chart n hW ≫ (pullbackIso n g).inv ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ hW.fromSpec := by
  rw [pullbackIso_inv_fst, pullbackIso_inv_snd, chart_over]
  exact ⟨chart_map n g hV hW e, rfl⟩

end AlgebraicGeometry.AffineSpace
