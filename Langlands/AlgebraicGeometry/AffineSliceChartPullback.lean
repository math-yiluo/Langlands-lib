import Langlands.AlgebraicGeometry.AffineLocalizedQuotientPullback

/-! # Comparing affine slice pullbacks with their ambient scheme pullbacks -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {U R : Scheme.{u}} (t : R ⟶ U)
    (V : U.Opens) (hV : IsAffineOpen V) (W : R.Opens) (hW : IsAffineOpen W)
    (hWt : W ≤ t ⁻¹ᵁ V) (I : Ideal Γ(U, V))

/-- The affine chart pullback is an open subspace of the ambient slice pullback. -/
def affineSliceChartToPullback :
    pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (t.appLE V W hWt)) ⟶
    pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec) t :=
  pullback.map _ _ _ _ (𝟙 _) hW.fromSpec hV.fromSpec
    (by simp) (hV.SpecMap_appLE_fromSpec t hW hWt)

instance isOpenImmersion_affineSliceChartToPullback :
    IsOpenImmersion (affineSliceChartToPullback t V hV W hW hWt I) := by
  unfold affineSliceChartToPullback
  infer_instance

@[reassoc (attr := simp)]
lemma affineSliceChartToPullback_snd :
    affineSliceChartToPullback t V hV W hW hWt I ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ hW.fromSpec := by
  simp only [affineSliceChartToPullback, pullback.map, pullback.lift_snd]

@[reassoc]
lemma affineSliceChartToPullback_comp (s : R ⟶ U) (hWs : W ≤ s ⁻¹ᵁ V) :
    affineSliceChartToPullback t V hV W hW hWt I ≫ (pullback.snd _ _ ≫ s) =
      (pullback.snd _ _ ≫ Spec.map (s.appLE V W hWs)) ≫ hV.fromSpec := by
  rw [← Category.assoc, affineSliceChartToPullback_snd, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec s hV hW hWs]
  simp only [Category.assoc]

end Langlands.AlgebraicGeometry
