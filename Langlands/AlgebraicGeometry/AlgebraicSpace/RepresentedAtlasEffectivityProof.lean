import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasEffectivityDescent
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Effective descent of four represented properties from a target étale atlas -/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace AtlasEffectivity

/-- A property stable under base change and descending along surjective étale maps descends
effectively from a target atlas whenever the atlas square forces every pullback of the space
map along a scheme point to be represented. -/
theorem etaleAtlasPropertyEffectivity_of_represented (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u})]
    (H : ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y) (U V : Over S)
      (a : (schemeYoneda S).obj U ⟶ X.presheaf) (b : (schemeYoneda S).obj V ⟶ Y.presheaf)
      (q : U ⟶ V), IsEtale b → IsSurjective b →
      IsPullback a ((schemeYoneda S).map q) (hom f) b → P q.left →
      ∀ (T : Over S) (g : (schemeYoneda S).obj T ⟶ Y.presheaf) (F : FppfSheaf S)
        (φ₁ : F.obj ⟶ X.presheaf) (φ₂ : F.obj ⟶ (schemeYoneda S).obj T),
        IsPullback φ₁ φ₂ (hom f) g → ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ F.obj)) :
    EtaleAtlasPropertyEffectivity P := by
  intro S X Y f U V a b q hbe hbs hsq hq
  have hr : IsRepresentableMorphism (hom f) :=
    isRepresentableMorphism_of_pullbacks f (H S X Y f U V a b q hbe hbs hsq hq)
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  let e := (schemeYoneda S).preimageIso (hsq.isoIsPullback _ _ (hr.isPullback b))
  have he : e.hom ≫ hr.snd b = q := (schemeYoneda S).map_injective (by
    rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage,
      IsPullback.isoIsPullback_hom_snd])
  have hP : P (((Over.forget S).mapIso e).hom ≫ (hr.snd b).left) := by
    change P (e.hom ≫ hr.snd b).left
    rwa [he]
  exact relativeProperty_of_etale_atlas P hr b hbe hbs
    ((MorphismProperty.cancel_left_of_respectsIso P _ _).mp hP)

end AtlasEffectivity

open AtlasEffectivity

/-- Closed immersions, affine morphisms, open immersions and finite morphisms of algebraic
spaces descend effectively from one surjective étale target atlas. -/
theorem representedAtlasEffectivity : RepresentedAtlasEffectivityStatement.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine etaleAtlasPropertyEffectivity_of_represented _ ?_
    intro S X Y f U V a b q hbe hbs hsq hq T g F φ₁ φ₂ hF
    have : _root_.AlgebraicGeometry.IsClosedImmersion q.left := hq
    exact exists_iso_of_isAffineHom hsq hbe hbs hF
  · refine etaleAtlasPropertyEffectivity_of_represented _ ?_
    intro S X Y f U V a b q hbe hbs hsq hq T g F φ₁ φ₂ hF
    have : IsAffineHom q.left := hq
    exact exists_iso_of_isAffineHom hsq hbe hbs hF
  · refine etaleAtlasPropertyEffectivity_of_represented _ ?_
    intro S X Y f U V a b q hbe hbs hsq hq T g F φ₁ φ₂ hF
    have : _root_.AlgebraicGeometry.IsOpenImmersion q.left := hq
    exact exists_iso_of_isOpenImmersion_test hsq hbe hbs hF
  · refine etaleAtlasPropertyEffectivity_of_represented _ ?_
    intro S X Y f U V a b q hbe hbs hsq hq T g F φ₁ φ₂ hF
    have : _root_.AlgebraicGeometry.IsFinite q.left := hq
    exact exists_iso_of_isAffineHom hsq hbe hbs hF

end Langlands.AlgebraicGeometry.AlgebraicSpace
