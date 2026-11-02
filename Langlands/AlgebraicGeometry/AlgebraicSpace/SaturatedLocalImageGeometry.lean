import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleImageSaturation
import Langlands.AlgebraicGeometry.AlgebraicSpace.CompactLocalImage
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedLocalImageGeometry

/-! # Scheme geometry of a compact represented saturation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open EtaleImageSaturation

variable {S : Scheme.{u}} {B T V : Over S}

/-- A compact scheme base change of a local image, retaining the morphism
geometry and a locally surjective projection to that image. -/
def SaturatedLocalImageGeometry {F : Presheaf S}
    (e : B ⟶ T) (f : F ⟶ (schemeYoneda S).obj T)
    (c : (schemeYoneda S).obj V ⟶ F) : Prop :=
  ∃ (W : Over S) (q : W ⟶ B)
    (k : (schemeYoneda S).obj W ⟶
      ((Subfunctor.range c).sheafify (fppfTopology S)).toFunctor),
    CompactSpace W.left ∧
    IsPullback k ((schemeYoneda S).map q)
      (((Subfunctor.range c).sheafify (fppfTopology S)).ι ≫ f)
      ((schemeYoneda S).map e) ∧
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) k ∧
    Mono q.left ∧ LocallyOfFiniteType q.left ∧ LocallyQuasiFinite q.left

set_option backward.isDefEq.respectTransparency false in
/-- A compact representation of the saturation supplies the geometric
scheme base change required by effective descent. -/
theorem saturatedLocalImageGeometry {F G : FppfSheaf S}
    (e : B ⟶ T) [Etale e.left]
    {π : G.obj ⟶ F.obj} {p : G.obj ⟶ (schemeYoneda S).obj B}
    (f : F.obj ⟶ (schemeYoneda S).obj T) [Mono f]
    (sq : IsPullback π p f ((schemeYoneda S).map e))
    (w : V ⟶ B) [LocallyOfFiniteType w.left]
    (a : (schemeYoneda S).obj V ⟶ G.obj) (haOpen : IsOpenImmersion a)
    (ha : a ≫ p = (schemeYoneda S).map w)
    (hR : CompactLocalImage.HasCompactRepresentation
      (((Subfunctor.range (a ≫ π)).sheafify (fppfTopology S)).preimage π)) :
    SaturatedLocalImageGeometry e f (a ≫ π) := by
  let A := (Subfunctor.range (a ≫ π)).sheafify (fppfTopology S)
  let R := A.preimage π
  let c := translate e w sq a ha
  let C := (Subfunctor.range c).sheafify (fppfTopology S)
  have hRC : R = C := by
    dsimp [R, A, C, c]
    rw [← OpenSubfunctorImages.sheafify_preimage,
      ← OpenSubfunctorLifting.range_eq_preimage_of_isPullback
        (translate_isPullback e w sq a ha)]
  have hC : CompactLocalImage.HasCompactRepresentation C := by
    rwa [← hRC]
  obtain ⟨W, hW, ⟨i⟩⟩ := hC
  let : Mono p := sq.mono_snd_of_mono
  have haEtale : IsEtale a := by
    apply MorphismProperty.relative_monotone
      (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
        (Over.forget S)) ?_ a haOpen
    intro U U' g hg
    let : _root_.AlgebraicGeometry.IsOpenImmersion g.left := hg
    exact inferInstanceAs (Etale g.left)
  have hπ : IsEtale π := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
        (schemeYoneda S)) sq.flip (isEtale_map e inferInstance)
  have hc : IsEtale c := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
        (schemeYoneda S)) (translate_isPullback e w sq a ha) (haEtale.comp hπ)
  have hnew : LocallyOfFiniteType (newBase e w).left := by
    apply MorphismProperty.of_isPullback (P := @LocallyOfFiniteType.{u})
      ((chartRelation_isPullback e w).map (Over.forget S))
    change LocallyOfFiniteType (w.left ≫ e.left)
    infer_instance
  let : LocallyOfFiniteType (newBase e w).left := hnew
  obtain ⟨q, d, hq, hd, hdq, hqm, hde, hds, hqft, hqlqf⟩ :=
    representedLocalImageGeometry c hc p (newBase e w)
      (translate_p e w sq a ha) i
  let g := i.hom ≫ C.ι
  have hg : Subfunctor.range g = R := by
    dsimp [g]
    rw [Subfunctor.range_comp, Subfunctor.range_eq_top i.hom,
      Subfunctor.image_top, Subfunctor.range_ι]
    exact hRC.symm
  have hkle : Subfunctor.range (g ≫ π) ≤ A := by
    rw [Subfunctor.range_comp, Subfunctor.image_le_iff, hg]
  let k := Subfunctor.lift (g ≫ π) hkle
  have hk : k ≫ A.ι = g ≫ π := Subfunctor.lift_ι _ _
  have sqR : IsPullback k g A.ι π :=
    OpenSubfunctorLifting.isPullback_subfunctor_of_range A k g π hk hg
  have hfinal : IsPullback k ((schemeYoneda S).map q)
      (A.ι ≫ f) ((schemeYoneda S).map e) := by
    rw [hq]
    exact sqR.paste_vert sq
  let aA := Subfunctor.toRangeSheafify (fppfTopology S) (a ≫ π)
  have haA : aA ≫ A.ι = a ≫ π := by
    ext U x
    rfl
  let s := sqR.lift aA a haA
  have hsk : s ≫ k = aA := sqR.lift_fst _ _ _
  have hks : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) k :=
    CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      (fppfTopology S) hsk
  exact ⟨W, q, k, hW, hfinal, hks, hqm, hqft, hqlqf⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
