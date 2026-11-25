/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy.Slope
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Preimages of charts of the blow-up

Preimages of the charts of the blow-up under the charts at other generators of the centre, and
closedness of the preimage of the range of a lift into a pullback
(`AlgebraicGeometry.Scheme.isClosed_preimage_range_pullbackLift`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry
section Closedness

/-! ### Closedness of the graph of the glued extension

The graph of the extension is checked to be closed one chart of the blow-up at a time: on
the chart at a generator `c` of the centre, the graph is cut out by the equations
`(d/c) · tⱼ = (bⱼ/c)` of `isClosed_range_of_basicOpen_fractions`. -/

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- **Composing the slopes across two charts**: on the chart at `a · d` the slope `b / d`
times the slope `d / a` is the slope `b / a`. -/
lemma AffineBlowup.awayMap_awaySlope_mul {a d b : A} (ha : a ∈ I) (hd : d ∈ I) (hb : b ∈ I) :
    HomogeneousLocalization.awayMap (reesGrading I) (reesX_mem I a ha)
        (mul_comm (reesX I a ha) (reesX I d hd)) (AffineBlowup.awaySlope I hd hb) *
      HomogeneousLocalization.awayMap (reesGrading I) (reesX_mem I d hd) rfl
        (AffineBlowup.awaySlope I ha hd) =
      HomogeneousLocalization.awayMap (reesGrading I) (reesX_mem I d hd) rfl
        (AffineBlowup.awaySlope I ha hb) := by
  rw [AffineBlowup.awayMap_awaySlope hd ha hb (mul_comm (reesX I a ha) (reesX I d hd)),
    AffineBlowup.awayMap_awaySlope ha hd hd rfl, AffineBlowup.awayMap_awaySlope ha hd hb rfl,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_one, Submonoid.coe_mul]
  ring

/-- The transition map into the chart at `a · b` has range the basic open of the slope
`b / a`. -/
lemma AffineBlowup.mem_range_specMap_awayMap_iff {a b : A} (ha : a ∈ I) (hb : b ∈ I)
    (y : Spec (.of (HomogeneousLocalization.Away (reesGrading I) (reesX I a ha)))) :
    (∃ z, Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading I)
      (reesX_mem I b hb) (rfl : reesX I a ha * reesX I b hb = _))) z = y) ↔
      y ∈ PrimeSpectrum.basicOpen (AffineBlowup.awaySlope I ha hb) := by
  let := (HomogeneousLocalization.awayMap (reesGrading I) (reesX_mem I b hb)
    (rfl : reesX I a ha * reesX I b hb = _)).toAlgebra
  have := HomogeneousLocalization.Away.isLocalization_mul (reesX_mem I a ha)
    (reesX_mem I b hb) rfl one_ne_zero
  rw [← AffineBlowup.isLocalizationElem_eq_awaySlope]
  exact Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range _ _) y

/-- The `a`-chart of the blow-up meets the `b`-chart in the basic open of the slope `b / a`. -/
lemma AffineBlowup.chart_preimage_opensRange {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    AffineBlowup.chart I (reesX I a ha) (reesX_mem I a ha) ⁻¹ᵁ
        (AffineBlowup.chart I (reesX I b hb) (reesX_mem I b hb)).opensRange =
      PrimeSpectrum.basicOpen (AffineBlowup.awaySlope I ha hb) := by
  rw [AffineBlowup.opensRange_chart, AffineBlowup.chart,
    Proj.awayι_preimage_basicOpen (𝒜 := reesGrading I) (reesX_mem I a ha) one_pos
      (reesX_mem I b hb) one_pos, AffineBlowup.isLocalizationElem_eq_awaySlope]

variable {X : Scheme.{u}}

/-- The `a`-chart of the blow-up over an affine open meets the `b`-chart in the basic open of
the slope `b / a`. -/
lemma Scheme.IdealSheafData.blowupChart_preimage_opensRange (K : X.IdealSheafData)
    (V : X.affineOpens) {a b : Γ(X, V.1)} (ha : a ∈ K.ideal V) (hb : b ∈ K.ideal V) :
    K.blowupChart V ha ⁻¹ᵁ (K.blowupChart V hb).opensRange =
      PrimeSpectrum.basicOpen (AffineBlowup.awaySlope (K.ideal V) ha hb) := by
  rw [← AffineBlowup.chart_preimage_opensRange ha hb]
  refine TopologicalSpace.Opens.ext (Set.ext fun y ↦ ?_)
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, (K.blowupι V).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact hz
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Scheme.IdealSheafData.blowupChart, Scheme.IdealSheafData.blowupChart,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz]

/-- **The graph of the extension, seen on one chart.** On the base change of a chart of the
blow-up, the graph of the extension is the graph of the chart-local morphism defined by the
coordinates of the extension. -/
lemma Scheme.isClosed_preimage_range_pullbackLift {X Bl : Scheme.{u}} {σ : Type u}
    (π : Bl ⟶ X) {W : Bl.Opens} (g : W.toScheme ⟶ 𝔸(σ; X))
    (hg : g ≫ 𝔸(σ; X) ↘ X = W.ι ≫ π)
    {R : CommRingCat.{u}} (chart : Spec R ⟶ Bl)
    (q : 𝔸(σ; Spec R) ⟶ pullback π (𝔸(σ; X) ↘ X)) [IsOpenImmersion q]
    (hq_fst : q ≫ pullback.fst π (𝔸(σ; X) ↘ X) = (𝔸(σ; Spec R) ↘ Spec R) ≫ chart)
    (hq_snd : q ≫ pullback.snd π (𝔸(σ; X) ↘ X) = AffineSpace.map σ (chart ≫ π))
    (lam : (chart ⁻¹ᵁ W).toScheme ⟶ W.toScheme)
    (hlam : lam ≫ W.ι = (chart ⁻¹ᵁ W).ι ≫ chart)
    (hcl : IsClosed (Set.range (AffineSpace.homOfVector (chart ⁻¹ᵁ W).ι
      (fun j ↦ (lam ≫ g).appTop (AffineSpace.coord X j))))) :
    IsClosed (q.base ⁻¹' Set.range (pullback.lift W.ι g hg.symm)) := by
  set del : (chart ⁻¹ᵁ W).toScheme ⟶ 𝔸(σ; Spec R) :=
    AffineSpace.homOfVector (chart ⁻¹ᵁ W).ι
      (fun j ↦ (lam ≫ g).appTop (AffineSpace.coord X j)) with hdeldef
  have hdel_over : del ≫ (𝔸(σ; Spec R) ↘ Spec R) = (chart ⁻¹ᵁ W).ι :=
    AffineSpace.homOfVector_over _ _
  have hdel_map : del ≫ AffineSpace.map σ (chart ≫ π) = lam ≫ g := by
    refine AffineSpace.homOfVector_coord_comp_map _ _ _ ?_
    rw [Category.assoc, hg, ← Category.assoc, hlam, Category.assoc]
  have hdelq : del ≫ q = lam ≫ pullback.lift W.ι g hg.symm := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hq_fst, ← Category.assoc, hdel_over, Category.assoc,
        pullback.lift_fst, hlam]
    · rw [Category.assoc, hq_snd, hdel_map, Category.assoc, pullback.lift_snd]
  have hpre : q.base ⁻¹' Set.range (pullback.lift W.ι g hg.symm) = Set.range del.base := by
    ext y
    constructor
    · rintro ⟨w, hw⟩
      have hfst : chart ((𝔸(σ; Spec R) ↘ Spec R) y) = W.ι w := by
        rw [← Scheme.Hom.comp_apply, ← hq_fst, Scheme.Hom.comp_apply, ← hw,
          ← Scheme.Hom.comp_apply, pullback.lift_fst]
      have hmemO : (𝔸(σ; Spec R) ↘ Spec R) y ∈ chart ⁻¹ᵁ W := by
        have hmem : chart ((𝔸(σ; Spec R) ↘ Spec R) y) ∈ W := by rw [hfst]; exact w.2
        exact hmem
      refine ⟨⟨(𝔸(σ; Spec R) ↘ Spec R) y, hmemO⟩, ?_⟩
      have hlw : lam ⟨(𝔸(σ; Spec R) ↘ Spec R) y, hmemO⟩ = w := by
        refine W.ι.isOpenEmbedding.injective ?_
        rw [← Scheme.Hom.comp_apply, hlam, Scheme.Hom.comp_apply]
        exact hfst
      refine q.isOpenEmbedding.injective ?_
      rw [← Scheme.Hom.comp_apply, hdelq, Scheme.Hom.comp_apply, hlw, hw]
    · rintro ⟨z, rfl⟩
      exact ⟨lam z, by rw [← Scheme.Hom.comp_apply, ← hdelq, Scheme.Hom.comp_apply]⟩
  rw [hpre]
  exact hcl

end Closedness

end AlgebraicGeometry
