import Langlands.AlgebraicGeometry.SchemeLimitRelativePropertyStatement
import Langlands.AlgebraicGeometry.SchemeFilteredPropertyProof
import Langlands.AlgebraicGeometry.SchemeLimitRelativeClosedImmersionProof

/-! # Relative smooth and flat descent -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.AffineLimit

open EtaleEquivalenceRelation.Action.TargetLimit
open SchemeLimitModel

private theorem affineTargetDiagramPropertyDescent
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hdesc : InitialRingModelPropertyDescent P)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (E F : I ⥤ Scheme.{u}) [∀ i, IsAffine (F.obj i)] (α : E ⟶ F)
    (cE : Cone E) (cF : Cone F) (hcF : IsLimit cF)
    (f : cE.pt ⟶ cF.pt) (i₀ : I)
    [LocallyOfFinitePresentation (α.app i₀)] [QuasiCompact (α.app i₀)]
    [QuasiSeparated (α.app i₀)]
    (hcart : ∀ {j : I} (r : j ⟶ i₀),
      IsPullback (E.map r) (α.app j) (α.app i₀) (F.map r))
    (hlim : IsPullback (cE.π.app i₀) f (α.app i₀) (cF.π.app i₀))
    (H : P f) : ∃ i, P (α.app i) := by
  have : IsAffine cF.pt := Scheme.isAffine_of_isLimit cF hcF
  have (i : Iᵒᵖ) : IsAffine (F.op.obj i).unop := by dsimp; infer_instance
  let A := F.op ⋙ Scheme.Γ
  let dA := Scheme.Γ.mapCocone cF.op
  have hcA : IsColimit dA := isColimitOfPreserves Scheme.Γ hcF.op
  let X₀ : Over (Spec (A.obj (op i₀))) :=
    Over.mk (α.app i₀ ≫ (F.obj i₀).isoSpec.hom)
  have : LocallyOfFinitePresentation X₀.hom := by dsimp [X₀]; infer_instance
  have : QuasiCompact X₀.hom := by dsimp [X₀]; infer_instance
  have : QuasiSeparated X₀.hom := by dsimp [X₀]; infer_instance
  have hpb : IsPullback (cE.π.app i₀) (f ≫ cF.pt.isoSpec.hom)
      X₀.hom (Spec.map (dA.ι.app (op i₀))) := by
    apply hlim.of_iso (Iso.refl _) (Iso.refl _) cF.pt.isoSpec (F.obj i₀).isoSpec
    · simp
    · simp
    · simp [X₀]
    · exact (Scheme.isoSpec_hom_naturality
        (X := cF.pt) (Y := F.obj i₀) (cF.π.app i₀)).symm
  have hP : P (pullback.fst (Spec.map (dA.ι.app (op i₀))) X₀.hom) := by
    rw [← hpb.flip.isoPullback_inv_fst]
    exact MorphismProperty.RespectsIso.precomp P _ _
      (MorphismProperty.RespectsIso.postcomp P _ _ H)
  obtain ⟨j, hj⟩ := (hdesc A dA hcA (op i₀) X₀).mp hP
  have hpj : IsPullback (E.map j.hom.unop)
      (α.app j.right.unop ≫ (F.obj j.right.unop).isoSpec.hom)
      X₀.hom (Spec.map (A.map j.hom)) := by
    apply (hcart j.hom.unop).of_iso (Iso.refl _) (Iso.refl _)
      (F.obj j.right.unop).isoSpec (F.obj i₀).isoSpec
    · simp
    · simp
    · simp [X₀]
    · exact (Scheme.isoSpec_hom_naturality (F.map j.hom.unop)).symm
  refine ⟨j.right.unop, ?_⟩
  apply (P.cancel_right_of_respectsIso _ (F.obj j.right.unop).isoSpec.hom).mp
  rw [← hpj.flip.isoPullback_hom_fst]
  exact MorphismProperty.RespectsIso.precomp P _ _ hj

private theorem exists_property_level_of_affine_target
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hdesc : InitialRingModelPropertyDescent P)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
    [IsAffine S] [IsAffine Y] [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (H : P (baseChangeMap a b f w p)) :
    ∃ i, P (baseChangeMap a b f w (t.app i)) := by
  let i₀ : I := Classical.choice (IsCofiltered.nonempty (C := I))
  have : LocallyOfFinitePresentation (baseChangeMap a b f w (t.app i₀)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (baseChangeMap_isPullback a b f w (t.app i₀)).flip inferInstance
  have : QuasiCompact (baseChangeMap a b f w (t.app i₀)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (baseChangeMap_isPullback a b f w (t.app i₀)).flip inferInstance
  have : QuasiSeparated (baseChangeMap a b f w (t.app i₀)) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (baseChangeMap_isPullback a b f w (t.app i₀)).flip inferInstance
  have : LocallyOfFinitePresentation ((SchemeLimitModel.Geometry.morphismDiagram a b f w D t).app i₀) :=
    ‹LocallyOfFinitePresentation (baseChangeMap a b f w (t.app i₀))›
  have : QuasiCompact ((SchemeLimitModel.Geometry.morphismDiagram a b f w D t).app i₀) :=
    ‹QuasiCompact (baseChangeMap a b f w (t.app i₀))›
  have : QuasiSeparated ((SchemeLimitModel.Geometry.morphismDiagram a b f w D t).app i₀) :=
    ‹QuasiSeparated (baseChangeMap a b f w (t.app i₀))›
  exact affineTargetDiagramPropertyDescent P hdesc
    (diagram D t a) (diagram D t b) (SchemeLimitModel.Geometry.morphismDiagram a b f w D t)
    (cone D t a c p hp) (cone D t b c p hp)
    (isLimitCone D t b c p hp hc) (baseChangeMap a b f w p) i₀
    (fun r ↦ (SchemeLimitModel.Geometry.morphismDiagram_cartesian a b f w D t r).flip)
    (cone_baseChangeMap_isPullback a b f w D t c p hp i₀).flip H

private theorem property_of_charts
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [IsZariskiLocalAtTarget P]
    {S X Y T : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    (p : T ⟶ S) (𝒰 : Y.OpenCover)
    (H : ∀ k, P
      (baseChangeMap (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
        (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl p)) :
    P (baseChangeMap a b f w p) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) (baseChangeCover b p 𝒰)
  intro k
  let h := chart_isPullback a b f w p (𝒰.f k)
  change P (pullback.snd (baseChangeMap a b f w p)
    (baseChangeMap (𝒰.f k ≫ b) b (𝒰.f k) rfl p))
  rw [← h.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp P _ _ (H k)

private theorem relativePropertyDescent
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [IsZariskiLocalAtTarget P]
    (hdesc : InitialRingModelPropertyDescent P) :
    RelativePropertyDescent P := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ c hc p hp
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  let 𝒰 := Y.affineCover.finiteSubcover
  constructor
  · intro H
    have hchart (k : 𝒰.I₀) :
        ∃ i, P
          (baseChangeMap (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
            (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl (t.app i)) := by
      let g := pullback.snd f (𝒰.f k)
      let z := g ≫ (𝒰.f k ≫ b)
      have hP : P (baseChangeMap z (𝒰.f k ≫ b) g rfl p) :=
        MorphismProperty.of_isPullback (P := P)
          (chart_isPullback a b f w p (𝒰.f k)) H
      exact exists_property_level_of_affine_target P hdesc D t
        z (𝒰.f k ≫ b) g rfl c hc p hp hP
    choose j hj using hchart
    obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
    let r (k : 𝒰.I₀) : i ⟶ j k := (hi (by simp)).some
    refine ⟨i, property_of_charts P a b f w (t.app i) 𝒰 ?_⟩
    intro k
    exact MorphismProperty.of_isPullback (P := P)
      (SchemeLimitModel.Geometry.morphismDiagram_cartesian
        (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
        (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl D t (r k)).flip (hj k)
  · rintro ⟨i, H⟩
    exact MorphismProperty.of_isPullback (P := P)
      (cone_baseChangeMap_isPullback a b f w D t c p hp i).flip H

/-- Relative smoothness descends chartwise to a common original level. -/
theorem relativeSmoothDescent : RelativeSmoothDescent.{u} :=
  relativePropertyDescent @Smooth initialRingModelSmoothDescent

/-- Relative flatness descends chartwise to a common original level. -/
theorem relativeFlatDescent : RelativeFlatDescent.{u} :=
  relativePropertyDescent @Flat initialRingModelFlatDescent

/-- Both relative properties descend along the actual affine scheme limit. -/
theorem relativeSmoothFlatDescent : RelativeSmoothFlatDescent.{u} :=
  ⟨relativeSmoothDescent, relativeFlatDescent⟩

end Langlands.AlgebraicGeometry.AffineLimit
