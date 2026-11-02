import Langlands.AlgebraicGeometry.AffineSliceChartPullback

/-! # Localized affine slices in ambient scheme pullbacks -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {U R : Scheme.{u}} (t : R ⟶ U)
    (V : U.Opens) (hV : IsAffineOpen V) (W : R.Opens) (hW : IsAffineOpen W)
    (hWt : W ≤ t ⁻¹ᵁ V) (I : Ideal Γ(U, V)) (g : Γ(R, W))

/-- A localized affine quotient slice enters the ambient slice pullback. -/
def affineLocalizedSliceChartToPullback :
    Spec (CommRingCat.of ((Localization.Away g) ⧸
      I.map ((algebraMap Γ(R, W) (Localization.Away g)).comp (t.appLE V W hWt).hom))) ⟶
    pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec) t :=
  affineLocalizedQuotientToPullback (t.appLE V W hWt).hom I g ≫
    affineSliceChartToPullback t V hV W hW hWt I

instance isOpenImmersion_affineLocalizedSliceChartToPullback :
    IsOpenImmersion (affineLocalizedSliceChartToPullback t V hV W hW hWt I g) := by
  unfold affineLocalizedSliceChartToPullback
  infer_instance

@[reassoc]
lemma affineLocalizedSliceChartToPullback_snd :
    affineLocalizedSliceChartToPullback t V hV W hW hWt I g ≫ pullback.snd _ _ =
      (affineLocalizedQuotientToPullback (t.appLE V W hWt).hom I g ≫
        pullback.snd _ _) ≫ hW.fromSpec := by
  rw [affineLocalizedSliceChartToPullback, Category.assoc,
    affineSliceChartToPullback_snd, ← Category.assoc]
  rfl

/-- Etaleness of the localized quotient for the separate map `s` gives an
etale neighborhood inside the ambient slice pullback. -/
lemma etale_affineLocalizedSliceChartToPullback_comp
    (s : R ⟶ U) (hWs : W ≤ s ⁻¹ᵁ V)
    (he : (((Ideal.Quotient.mk
      (I.map ((algebraMap Γ(R, W) (Localization.Away g)).comp (t.appLE V W hWt).hom))).comp
        (algebraMap Γ(R, W) (Localization.Away g))).comp (s.appLE V W hWs).hom).Etale) :
    Etale (affineLocalizedSliceChartToPullback t V hV W hW hWt I g ≫
      (pullback.snd _ _ ≫ s)) := by
  rw [affineLocalizedSliceChartToPullback, Category.assoc,
    affineSliceChartToPullback_comp t V hV W hW hWt I s hWs, ← Category.assoc]
  let := etale_affineLocalizedQuotientToPullback_comp
    (s.appLE V W hWs).hom (t.appLE V W hWt).hom I g he
  infer_instance

/-- An allowed source prime lifts to a formally etale stalk of the full
scheme pullback when the localized quotient is etale for `s`. -/
lemma exists_formallyEtale_stalk_sliceChart
    (s : R ⟶ U) (hWs : W ≤ s ⁻¹ᵁ V)
    (q : Spec (CommRingCat.of Γ(R, W))) (hg : g ∉ q.asIdeal)
    (hI : I ≤ q.asIdeal.comap (t.appLE V W hWt).hom)
    (he : (((Ideal.Quotient.mk
      (I.map ((algebraMap Γ(R, W) (Localization.Away g)).comp (t.appLE V W hWt).hom))).comp
        (algebraMap Γ(R, W) (Localization.Away g))).comp (s.appLE V W hWs).hom).Etale) :
    ∃ b : (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec)
      t : Scheme.{u}),
      (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec) t)
        b = hW.fromSpec q ∧
      ((pullback.snd _ _ ≫ s).stalkMap b).hom.FormallyEtale := by
  obtain ⟨z, hz⟩ :=
    exists_affineLocalizedQuotientPoint (t.appLE V W hWt).hom I g q hg hI
  let := etale_affineLocalizedSliceChartToPullback_comp t V hV W hW hWt I g s hWs he
  refine ⟨affineLocalizedSliceChartToPullback t V hV W hW hWt I g z, ?_,
    formallyEtale_stalk_of_etale_open _ _ z⟩
  change (affineLocalizedSliceChartToPullback t V hV W hW hWt I g ≫
    pullback.snd _ _) z = _
  rw [affineLocalizedSliceChartToPullback_snd, Scheme.Hom.comp_apply, hz]

/-- Finitely many equations define a locally finitely presented chart slice. -/
lemma locallyOfFinitePresentation_affineQuotientChart (hI : I.FG) :
    LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec) := by
  let : Algebra.FinitePresentation Γ(U, V) (Γ(U, V) ⧸ I) :=
    Algebra.FinitePresentation.quotient hI
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    change (algebraMap Γ(U, V) (Γ(U, V) ⧸ I)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  infer_instance

end Langlands.AlgebraicGeometry
