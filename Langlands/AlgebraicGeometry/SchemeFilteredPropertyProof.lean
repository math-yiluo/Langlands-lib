import Langlands.AlgebraicGeometry.SchemeFilteredPropertyStatement
import Langlands.AlgebraicGeometry.SchemeFilteredPropertyModelProof
import Langlands.AlgebraicGeometry.SchemeFilteredModelProof

/-! # Eventual properties of prescribed original-ring models -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

private theorem initialRingModelPropertyDescent
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hmodel : SchemeFilteredPropertyModelExistence P) :
    InitialRingModelPropertyDescent P := by
  intro J _ _ F c hc j₀ X _ _ _
  let p := Spec.map (c.ι.app j₀)
  let g := pullback.fst p X.hom
  constructor
  · intro hg
    let F' := Under.forget j₀ ⋙ F
    let c' := c.whisker (Under.forget j₀)
    have hc' : IsColimit c' :=
      (Functor.Final.isColimitWhiskerEquiv (Under.forget j₀) c).symm hc
    obtain ⟨j, Y, b, π, hfp, hqc, hqs, hb, hpb⟩ :=
      hmodel (Under j₀) F' c' hc' (pullback p X.hom) g hg
    let : LocallyOfFinitePresentation b := hfp
    let : QuasiCompact b := hqc
    let : QuasiSeparated b := hqs
    let q := Spec.map (c.ι.app j.right)
    let r := Spec.map (F.map j.hom)
    let Xj : Over (Spec (F.obj j.right)) := Over.mk (pullback.fst r X.hom)
    let Yj : Over (Spec (F.obj j.right)) := Over.mk b
    let : QuasiCompact Xj.hom := by dsimp [Xj]; infer_instance
    let : QuasiSeparated Xj.hom := by dsimp [Xj]; infer_instance
    let : LocallyOfFinitePresentation Xj.hom := by dsimp [Xj]; infer_instance
    let : QuasiCompact Yj.hom := hqc
    let : QuasiSeparated Yj.hom := hqs
    let : LocallyOfFinitePresentation Yj.hom := hfp
    have hpbY : IsPullback π g Yj.hom q := hpb
    have hqr : q ≫ r = p := by
      dsimp [q, r, p]
      rw [← Spec.map_comp, c.w j.hom]
    have houter : IsPullback (pullback.snd p X.hom) g X.hom (q ≫ r) :=
      hqr.symm ▸ (IsPullback.of_hasPullback p X.hom).flip
    have hright : IsPullback (pullback.snd r X.hom) Xj.hom X.hom r :=
      (IsPullback.of_hasPullback r X.hom).flip
    have hpbX := houter.of_right' hright
    let e : pullback q Xj.hom ≅ pullback q Yj.hom :=
      hpbX.flip.isoPullback.symm ≪≫ hpbY.flip.isoPullback
    have he : e.hom ≫ pullback.fst q Yj.hom = pullback.fst q Xj.hom := by
      simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_inv_fst]
    obtain ⟨k, ek, hek, _⟩ :=
      (initialRingModelMorphismDescent F c hc j.right Xj Yj).2.2
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance e he
    let s := Spec.map (F.map k.hom)
    have hY : P (pullback.fst s Yj.hom) := MorphismProperty.pullback_fst _ _ hb
    have hX : P (pullback.fst s Xj.hom) := by
      rw [← hek]
      exact MorphismProperty.RespectsIso.precomp P _ _ hY
    let htotal := (IsPullback.of_hasPullback s Xj.hom).paste_vert
      (IsPullback.of_hasPullback r X.hom)
    refine ⟨Under.mk (j.hom ≫ k.hom), ?_⟩
    have hsr : Spec.map (F.map (j.hom ≫ k.hom)) = s ≫ r := by
      simp only [Functor.map_comp, Spec.map_comp, s, r]
    change P (pullback.fst (Spec.map (F.map (j.hom ≫ k.hom))) X.hom)
    rw [hsr, ← htotal.isoPullback_inv_fst]
    exact MorphismProperty.RespectsIso.precomp P _ _ hX
  · rintro ⟨j, hj⟩
    let q := Spec.map (c.ι.app j.right)
    let r := Spec.map (F.map j.hom)
    have hqr : q ≫ r = p := by
      dsimp [q, r, p]
      rw [← Spec.map_comp, c.w j.hom]
    have houter : IsPullback (pullback.snd p X.hom) g X.hom (q ≫ r) :=
      hqr.symm ▸ (IsPullback.of_hasPullback p X.hom).flip
    have hright : IsPullback (pullback.snd r X.hom)
        (pullback.fst r X.hom) X.hom r :=
      (IsPullback.of_hasPullback r X.hom).flip
    exact MorphismProperty.of_isPullback (P := P) (houter.of_right' hright) hj

/-- Smoothness holds eventually for the prescribed model. -/
theorem initialRingModelSmoothDescent : InitialRingModelSmoothDescent.{u} :=
  initialRingModelPropertyDescent @Smooth schemeFilteredSmoothModelExistence

/-- Flatness holds eventually for the prescribed model. -/
theorem initialRingModelFlatDescent : InitialRingModelFlatDescent.{u} :=
  initialRingModelPropertyDescent @Flat schemeFilteredFlatModelExistence

/-- Both eventual structural properties, along actual original maps. -/
theorem initialRingModelSmoothFlatDescent : InitialRingModelSmoothFlatDescent.{u} :=
  ⟨initialRingModelSmoothDescent, initialRingModelFlatDescent⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
