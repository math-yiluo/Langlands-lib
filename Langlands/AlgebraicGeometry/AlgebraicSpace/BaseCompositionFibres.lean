import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProduct

/-! # Geometric fibres after composition of bases -/

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition

variable {S T : Scheme.{u}} (g : S ⟶ T)

/-- The original fibre presheaf, composed to `T`, is the fibre of the composed morphism. -/
def pullbackFromSchemeIso {F G : Presheaf S} (f : F ⟶ G) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ G) :
    presheaf g (Limits.pullback f a) ≅ Limits.pullback (map g f) (fromScheme g a) := by
  have h : IsPullback (map g (pullback.fst f a))
      (map g (pullback.snd f a) ≫ (schemeIso g U).inv) (map g f) (fromScheme g a) := by
    apply (map_isPullback g (IsPullback.of_hasPullback f a)).of_iso'
      (Iso.refl _) (Iso.refl _) (schemeIso g U) (Iso.refl _)
    · simp
    · simp
    · simp
    · simp [fromScheme]
  exact h.isoPullback

/-- Every scheme fibre of a morphism of spaces has an actual etale-surjective scheme atlas. -/
theorem exists_atlas_pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf) :
    ∃ (V : Over S) (b : (schemeYoneda S).obj V ⟶ Limits.pullback (hom f) a),
      IsEtale b ∧ IsSurjective b := by
  let a' : (schemeToSpace S).obj U ⟶ Y := homMk a
  let e := FibreProduct.presheafIso f a'
  obtain ⟨V, b, hb, hs⟩ := (fibreProduct f a').property.2
  exact ⟨V, b ≫ e.hom, hb.comp_iso e, hs.comp_iso e⟩

/-- Quasi-compactness of a general space morphism survives composition of bases. -/
theorem quasiCompact_spaceMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsQuasiCompactMorphism f) : IsQuasiCompactMorphism (spaceMap g f) := by
  intro U hU α
  obtain ⟨V, t, rfl⟩ := U.mk_surjective
  generalize he : uliftYonedaEquiv.{u + 1} α = x
  rcases x with ⟨⟨s, y⟩, hs⟩
  change V ⟶ S at s
  have hst : s ≫ g = t := congrArg ULift.down hs
  subst t
  let US : Over S := Over.mk s
  let α' : (schemeYoneda S).obj US ⟶ Y.presheaf := uliftYonedaEquiv.{u + 1}.symm y
  have hα : α = fromScheme g α' := by
    apply uliftYonedaEquiv.{u + 1}.injective
    calc
      uliftYonedaEquiv.{u + 1} α = liftSection g Y.presheaf US y := he
      _ = uliftYonedaEquiv.{u + 1} (fromScheme g α') :=
        ((fromScheme_section g α').trans (congrArg (liftSection g Y.presheaf US)
          (uliftYonedaEquiv.{u + 1}.apply_symm_apply y))).symm
  rw [hα]
  obtain ⟨W, a, hW, ha, hs⟩ := hf US hU α'
  let e := pullbackFromSchemeIso g (hom f) α'
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨(Over.map g).obj W, fromScheme g a ≫ e.hom, hW,
    IsEtale.comp_iso (relative_fromScheme g _ ha) e,
    IsSurjective.comp_iso (relative_fromScheme g _ hs) e⟩

/-- All field-valued geometric fibres retain their connected ordinary point spaces. -/
theorem geometricallyConnectedFibres_spaceMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : HasGeometricallyConnectedFibres f) :
    HasGeometricallyConnectedFibres (spaceMap g f) := by
  intro K hK t α
  generalize he : uliftYonedaEquiv.{u + 1} α = x
  rcases x with ⟨⟨s, y⟩, hs⟩
  change Spec (CommRingCat.of K) ⟶ S at s
  have hst : s ≫ g = t := congrArg ULift.down hs
  subst t
  let US : Over S := Over.mk s
  let α' : (schemeYoneda S).obj US ⟶ Y.presheaf := uliftYonedaEquiv.{u + 1}.symm y
  have hα : α = fromScheme g α' := by
    apply uliftYonedaEquiv.{u + 1}.injective
    calc
      uliftYonedaEquiv.{u + 1} α = liftSection g Y.presheaf US y := he
      _ = uliftYonedaEquiv.{u + 1} (fromScheme g α') :=
        ((fromScheme_section g α').trans (congrArg (liftSection g Y.presheaf US)
          (uliftYonedaEquiv.{u + 1}.apply_symm_apply y))).symm
  rw [hα]
  obtain ⟨W, a, ha, hs⟩ := exists_atlas_pullback f α'
  let := pointTopology (Limits.pullback (hom f) α')
  let := pointTopology (presheaf g (Limits.pullback (hom f) α'))
  let := pointTopology (Limits.pullback (map g (hom f)) (fromScheme g α'))
  have hc := hf K s α'
  let e := (pointsHomeomorphOfAtlas g a ha hs).trans
    (Points.isoHomeomorph (pullbackFromSchemeIso g (hom f) α'))
  exact e.connectedSpace_iff.mp hc

end Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition
