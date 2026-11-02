import Langlands.AlgebraicGeometry.Picard.SmoothArrowKernel
import Langlands.AlgebraicGeometry.Picard.AtlasArrowInversion

/-! # The actual smooth scheme equivalence relation on Picard arrows -/

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))

/-- The full pair of actual arrows with identical endpoint maps. -/
def atlasArrowKernelPresheaf : AlgebraicSpace.Presheaf S :=
  Limits.pullback (atlasArrowEndpoint f L) (atlasArrowEndpoint f L)

/-- The first actual arrow of an endpoint-kernel section. -/
def atlasArrowKernelFst : atlasArrowKernelPresheaf f L ⟶ atlasArrowPresheaf f L :=
  Limits.pullback.fst _ _

/-- The second actual arrow of an endpoint-kernel section. -/
def atlasArrowKernelSnd : atlasArrowKernelPresheaf f L ⟶ atlasArrowPresheaf f L :=
  Limits.pullback.snd _ _

/-- The full actual endpoint kernel is effective as a presheaf kernel pair. -/
lemma atlasArrowKernel_isPullback :
    IsPullback (atlasArrowKernelFst f L) (atlasArrowKernelSnd f L)
      (atlasArrowEndpoint f L) (atlasArrowEndpoint f L) :=
  IsPullback.of_hasPullback _ _

/-- A full scheme representative of arrows gives an actual scheme endpoint
kernel, with both scheme projections smooth under the actual automorphism hypothesis. -/
lemma exists_smoothArrowKernelScheme {A : Over S}
    (eA : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasArrowPresheaf f L)
    (h : HasSmoothRelativeAutomorphismSchemes f) :
    ∃ (R : Over S) (r s : R ⟶ A)
      (eR : (AlgebraicSpace.schemeYoneda S).obj R ≅ atlasArrowKernelPresheaf f L),
      eR.hom ≫ atlasArrowKernelFst f L = (AlgebraicSpace.schemeYoneda S).map r ≫ eA.hom ∧
      eR.hom ≫ atlasArrowKernelSnd f L = (AlgebraicSpace.schemeYoneda S).map s ≫ eA.hom ∧
      Smooth r.left ∧ Smooth s.left ∧
      IsPullback ((AlgebraicSpace.schemeYoneda S).map r)
        ((AlgebraicSpace.schemeYoneda S).map s)
        (eA.hom ≫ atlasArrowEndpoint f L) (eA.hom ≫ atlasArrowEndpoint f L) := by
  let hs := smooth_endpointKernel_projection f L (atlasArrowKernel_isPullback f L) h
  let hr := smooth_endpointKernel_projection f L (atlasArrowKernel_isPullback f L).flip h
  let hf : AlgebraicSpace.IsRepresentableMorphism (atlasArrowKernelSnd f L) := hs.1
  let R := hf.pullback eA.hom
  let s : R ⟶ A := hf.snd eA.hom
  have hPB := hf.isPullback eA.hom
  have : IsIso (hf.fst eA.hom) := hPB.isIso_fst_of_isIso
  let eR : (AlgebraicSpace.schemeYoneda S).obj R ≅ atlasArrowKernelPresheaf f L :=
    asIso (hf.fst eA.hom)
  let r : R ⟶ A := (AlgebraicSpace.schemeYoneda S).preimage
    (eR.hom ≫ atlasArrowKernelFst f L ≫ eA.inv)
  have hrf : eR.hom ≫ atlasArrowKernelFst f L =
      (AlgebraicSpace.schemeYoneda S).map r ≫ eA.hom := by
    dsimp only [r]
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hsf : eR.hom ≫ atlasArrowKernelSnd f L =
      (AlgebraicSpace.schemeYoneda S).map s ≫ eA.hom := hPB.w
  have hPBr : IsPullback eR.hom ((AlgebraicSpace.schemeYoneda S).map r)
      (atlasArrowKernelFst f L) eA.hom := IsPullback.of_horiz_isIso ⟨hrf⟩
  refine ⟨R, r, s, eR, hrf, hsf, hr.2 eA.hom eR.hom r hPBr,
    hs.2 eA.hom (hf.fst eA.hom) s hPB, ?_⟩
  exact (atlasArrowKernel_isPullback f L).of_iso' eR eA eA (Iso.refl _)
    hrf hsf (by simp) (by simp)

/-- Every represented presheaf kernel is a monomorphic equivalence relation
on the complete section type of every test scheme. -/
lemma representedKernel_sectionwise {A R : Over S} (r s : R ⟶ A)
    {E : AlgebraicSpace.Presheaf S} (c : (AlgebraicSpace.schemeYoneda S).obj A ⟶ E)
    (h : IsPullback ((AlgebraicSpace.schemeYoneda S).map r)
      ((AlgebraicSpace.schemeYoneda S).map s) c c) :
    ∀ T : Over S,
      Function.Injective (fun z : ((AlgebraicSpace.schemeYoneda S).obj R).obj (op T) ↦
        (((AlgebraicSpace.schemeYoneda S).map r).app (op T) z,
          ((AlgebraicSpace.schemeYoneda S).map s).app (op T) z)) ∧
      Equivalence (fun x y : ((AlgebraicSpace.schemeYoneda S).obj A).obj (op T) ↦
        ∃ z : ((AlgebraicSpace.schemeYoneda S).obj R).obj (op T),
          ((AlgebraicSpace.schemeYoneda S).map r).app (op T) z = x ∧
            ((AlgebraicSpace.schemeYoneda S).map s).app (op T) z = y) := by
  intro T
  have hT := h.app (op T)
  constructor
  · intro z w hzw
    exact Types.ext_of_isPullback hT (congrArg Prod.fst hzw) (congrArg Prod.snd hzw)
  · have hiff (x y : ((AlgebraicSpace.schemeYoneda S).obj A).obj (op T)) :
        (∃ z : ((AlgebraicSpace.schemeYoneda S).obj R).obj (op T),
          ((AlgebraicSpace.schemeYoneda S).map r).app (op T) z = x ∧
            ((AlgebraicSpace.schemeYoneda S).map s).app (op T) z = y) ↔
          c.app (op T) x = c.app (op T) y := by
      constructor
      · rintro ⟨z, rfl, rfl⟩
        exact ConcreteCategory.congr_hom hT.w z
      · exact Types.exists_of_isPullback hT x y
    exact ⟨fun x ↦ (hiff x x).mpr rfl,
      fun {x y} hxy ↦ (hiff y x).mpr ((hiff x y).mp hxy).symm,
      fun {x y z} hxy hyz ↦ (hiff x z).mpr (((hiff x y).mp hxy).trans ((hiff y z).mp hyz))⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
