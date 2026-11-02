import Langlands.AlgebraicGeometry.Picard.SmoothArrowKernelScheme
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement

/-! # Picard arrow relations as inputs to the smooth quotient construction -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open AlgebraicSpace.SmoothRelationQuotient

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))

/-- Local finite type of the object atlas passes to every smooth arrow endpoint. -/
lemma atlasArrowScheme_locallyOfFiniteType {A : Over S} (t : A ⟶ U)
    (ht : Smooth t.left) (hU : LocallyOfFiniteType U.hom) :
    LocallyOfFiniteType A.hom := by
  let : Smooth t.left := ht
  let : LocallyOfFiniteType U.hom := hU
  rw [← Over.w t]
  infer_instance

/-- The complete represented endpoint kernel has the generic relation property. -/
lemma representedKernel_isEquivalenceRelation {A R : Over S} (r s : R ⟶ A)
    {E : AlgebraicSpace.Presheaf S} (c : (AlgebraicSpace.schemeYoneda S).obj A ⟶ E)
    (h : IsPullback ((AlgebraicSpace.schemeYoneda S).map r)
      ((AlgebraicSpace.schemeYoneda S).map s) c c) :
    IsEquivalenceRelation ((AlgebraicSpace.schemeToSpace S).obj R)
      ((AlgebraicSpace.schemeYoneda S).map r)
      ((AlgebraicSpace.schemeYoneda S).map s) :=
  representedKernel_sectionwise r s c h

/-- Smooth scheme projections satisfy the generic common-etale-atlas condition. -/
lemma schemeRelation_hasSmoothProjections {A R : Over S} (r s : R ⟶ A)
    (hr : Smooth r.left) (hs : Smooth s.left) :
    HasSmoothProjections ((AlgebraicSpace.schemeToSpace S).obj R)
      ((AlgebraicSpace.schemeYoneda S).map r)
      ((AlgebraicSpace.schemeYoneda S).map s) := by
  refine ⟨R, 𝟙 _, r, s, ?_, ?_, ?_, ?_, hr, hs⟩
  · change (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (AlgebraicSpace.schemeYoneda S) (𝟙 _)
    let : MorphismProperty.RespectsIso (@Etale.{u}) :=
      Etale.etale_isStableUnderBaseChange.respectsIso
    let := MorphismProperty.RespectsIso.inverseImage (@Etale.{u}) (Over.forget S)
    apply MorphismProperty.relative.of_exists
    intro V g
    refine ⟨V, g, 𝟙 V, ?_, ?_⟩
    · simpa using IsPullback.of_id_snd (f := g)
    · change Etale (𝟙 V.left)
      infer_instance
  · change (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (AlgebraicSpace.schemeYoneda S) (𝟙 _)
    let := MorphismProperty.RespectsIso.inverseImage (@Surjective.{u}) (Over.forget S)
    apply MorphismProperty.relative.of_exists
    intro V g
    refine ⟨V, g, 𝟙 V, ?_, ?_⟩
    · simpa using IsPullback.of_id_snd (f := g)
    · change Surjective (𝟙 V.left)
      infer_instance
  · exact Category.id_comp _
  · exact Category.id_comp _

/-- The actual Picard presentation supplies the full input data of the first
smooth-relation quotient, while retaining both original smooth surjective endpoints. -/
lemma exists_smoothArrowRelation
    (hL : IsSmoothSurjectivePresentation f L)
    (hU : LocallyOfFiniteType U.hom) (hAut : HasSmoothRelativeAutomorphismSchemes f) :
    ∃ (A R : Over S) (a b : A ⟶ U) (r s : R ⟶ A)
      (eA : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasArrowPresheaf f L)
      (eR : (AlgebraicSpace.schemeYoneda S).obj R ≅ atlasArrowKernelPresheaf f L),
      eA.hom ≫ atlasArrowFst f L = (AlgebraicSpace.schemeYoneda S).map a ∧
      eA.hom ≫ atlasArrowSnd f L = (AlgebraicSpace.schemeYoneda S).map b ∧
      Smooth a.left ∧ Surjective a.left ∧ Smooth b.left ∧ Surjective b.left ∧
      eR.hom ≫ atlasArrowKernelFst f L = (AlgebraicSpace.schemeYoneda S).map r ≫ eA.hom ∧
      eR.hom ≫ atlasArrowKernelSnd f L = (AlgebraicSpace.schemeYoneda S).map s ≫ eA.hom ∧
      Smooth r.left ∧ Smooth s.left ∧
      IsPullback ((AlgebraicSpace.schemeYoneda S).map r)
        ((AlgebraicSpace.schemeYoneda S).map s)
        (eA.hom ≫ atlasArrowEndpoint f L) (eA.hom ≫ atlasArrowEndpoint f L) ∧
      LocallyOfFiniteType A.hom ∧
      IsEquivalenceRelation ((AlgebraicSpace.schemeToSpace S).obj R)
        ((AlgebraicSpace.schemeYoneda S).map r)
        ((AlgebraicSpace.schemeYoneda S).map s) ∧
      HasSmoothProjections ((AlgebraicSpace.schemeToSpace S).obj R)
        ((AlgebraicSpace.schemeYoneda S).map r)
        ((AlgebraicSpace.schemeYoneda S).map s) := by
  obtain ⟨A, a, b, eA, ha, hb, hsa, hsurja, hsb, hsurjb⟩ :=
    exists_atlasArrowScheme f L hL
  obtain ⟨R, r, s, eR, hr, hs, hsr, hss, hPB⟩ :=
    exists_smoothArrowKernelScheme f L eA hAut
  exact ⟨A, R, a, b, r, s, eA, eR, ha, hb, hsa, hsurja, hsb, hsurjb,
    hr, hs, hsr, hss, hPB, atlasArrowScheme_locallyOfFiniteType b hsb hU,
    representedKernel_isEquivalenceRelation r s _ hPB,
    schemeRelation_hasSmoothProjections r s hsr hss⟩

/-- The fixed etale sheafification of classes of arrows with equal endpoints.
Its geometric properties are separate obligations. -/
def arrowKernelQuotientSheaf {A R : Over S} (r s : R ⟶ A)
    (eA : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasArrowPresheaf f L)
    (h : IsPullback ((AlgebraicSpace.schemeYoneda S).map r)
      ((AlgebraicSpace.schemeYoneda S).map s)
      (eA.hom ≫ atlasArrowEndpoint f L) (eA.hom ≫ atlasArrowEndpoint f L)) :
    Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
  quotientSheaf ((AlgebraicSpace.schemeToSpace S).obj R)
    ((AlgebraicSpace.schemeYoneda S).map r)
    ((AlgebraicSpace.schemeYoneda S).map s)
    (representedKernel_isEquivalenceRelation r s _ h)

/-- The actual canonical map from all represented arrows to this etale quotient. -/
def arrowKernelQuotientMap {A R : Over S} (r s : R ⟶ A)
    (eA : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasArrowPresheaf f L)
    (h : IsPullback ((AlgebraicSpace.schemeYoneda S).map r)
      ((AlgebraicSpace.schemeYoneda S).map s)
      (eA.hom ≫ atlasArrowEndpoint f L) (eA.hom ≫ atlasArrowEndpoint f L)) :
    (AlgebraicSpace.schemeYoneda S).obj A ⟶
      (arrowKernelQuotientSheaf f L r s eA h).obj :=
  quotientMap ((AlgebraicSpace.schemeToSpace S).obj R)
    ((AlgebraicSpace.schemeYoneda S).map r)
    ((AlgebraicSpace.schemeYoneda S).map s)
    (representedKernel_isEquivalenceRelation r s _ h)

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
