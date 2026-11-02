import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleLocalImageInduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SaturatedLocalImageGeometry
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.QuasiAffineChart

/-! # Effective descent and compact representation of etale chart images -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleLocalImageDescent

open CompactLocalImage

variable {S : Scheme.{u}}

/-- Effective descent supplies the exact interface used by the finite-fibre induction. -/
theorem compactImageDescent : EtaleLocalImageInduction.CompactImageDescent S := by
  intro B T V _ _ _ e _ F G π p f _ sq a haOpen w _ ha hR
  let A := (Subfunctor.range (a ≫ π)).sheafify (fppfTopology S)
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
  have hAOpen : IsOpenImmersion A.ι :=
    OpenSubfunctorImages.sheafify_range_open (a ≫ π) (haEtale.comp hπ)
  have hAsh : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) A.toFunctor :=
    OpenSubfunctorImages.isSheaf_of_open F.property hAOpen
  obtain ⟨W, q, k, hW, hsq, hk, hqm, hqft, hqlqf⟩ :=
    saturatedLocalImageGeometry e f sq w a haOpen ha hR
  let : CompactSpace W.left := hW
  let : Mono q.left := hqm
  let : LocallyOfFiniteType q.left := hqft
  let : LocallyQuasiFinite q.left := hqlqf
  have : W.left.IsQuasiAffine :=
    LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite q.left
  obtain ⟨Y, r, i, hi⟩ :=
    LocallyQuasiFiniteDescent.exists_iso_of_quasiAffine
      (F := ⟨A.toFunctor, hAsh⟩) hsq hk (𝟙 T.left) e.left (by simp)
  have hr : (schemeYoneda S).map r = k ≫ i.inv := by
    calc
      (schemeYoneda S).map r =
          ((schemeYoneda S).map r ≫ i.hom) ≫ i.inv := by simp
      _ = k ≫ i.inv := by rw [hi]
  have hkEtale : IsEtale k := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
        (schemeYoneda S)) hsq.flip (isEtale_map e inferInstance)
  have hrEtale : IsEtale ((schemeYoneda S).map r) := by
    rw [hr]
    exact hkEtale.comp_iso i.symm
  have : Etale r.left :=
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
      (F := schemeYoneda S) hrEtale
  have hrLocal : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      ((schemeYoneda S).map r) := by
    rw [hr]
    let := hk
    infer_instance
  have hrSurj : Surjective r.left :=
    OpenSubfunctorImages.scheme_surjective_of_isLocallySurjective r hrLocal
  have hY : CompactSpace Y.left := by
    constructor
    rw [← Set.range_eq_univ.mpr hrSurj.surj]
    exact isCompact_range r.left.continuous
  exact ⟨Y, hY, ⟨i⟩⟩

/-- An affine open chart after an affine etale base change has a compact represented
local image, with no global surjectivity requirement on that base change. -/
theorem of_affine_etale
    {B T V : Over S} [IsAffine B.left] [IsAffine T.left] [IsAffine V.left]
    (e : B ⟶ T) [Etale e.left] {F G : FppfSheaf S}
    {π : G.obj ⟶ F.obj} {p : G.obj ⟶ (schemeYoneda S).obj B}
    {f : F.obj ⟶ (schemeYoneda S).obj T} [Mono f]
    (sq : IsPullback π p f ((schemeYoneda S).map e))
    (a : (schemeYoneda S).obj V ⟶ G.obj) (haOpen : IsOpenImmersion a)
    (w : V ⟶ B) [LocallyOfFiniteType w.left]
    (ha : a ≫ p = (schemeYoneda S).map w) :
    HasCompactRepresentation
      ((Subfunctor.range (a ≫ π)).sheafify (fppfTopology S)) :=
  EtaleLocalImageInduction.of_affine_etale compactImageDescent e sq a haOpen w ha

/-- A chosen compact scheme and an actual representing isomorphism for the
local image of an affine open chart after an affine etale base change. -/
def affineEtaleImageModel
    {B T V : Over S} [IsAffine B.left] [IsAffine T.left] [IsAffine V.left]
    (e : B ⟶ T) [Etale e.left] {F G : FppfSheaf S}
    {π : G.obj ⟶ F.obj} {p : G.obj ⟶ (schemeYoneda S).obj B}
    {f : F.obj ⟶ (schemeYoneda S).obj T} [Mono f]
    (sq : IsPullback π p f ((schemeYoneda S).map e))
    (a : (schemeYoneda S).obj V ⟶ G.obj) (haOpen : IsOpenImmersion a)
    (w : V ⟶ B) [LocallyOfFiniteType w.left]
    (ha : a ≫ p = (schemeYoneda S).map w) :
    Σ Y : {Y : Over S // CompactSpace Y.left},
      (schemeYoneda S).obj Y.val ≅
        ((Subfunctor.range (a ≫ π)).sheafify (fppfTopology S)).toFunctor :=
  let h := of_affine_etale e sq a haOpen w ha
  ⟨⟨Classical.choose h, (Classical.choose_spec h).1⟩,
    Classical.choice (Classical.choose_spec h).2⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleLocalImageDescent
