import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineAtlasChartReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedLocalImageGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.CompactLocalImage
import Langlands.AlgebraicGeometry.AlgebraicSpace.MonomorphismLocallyFiniteTypeSchemeStatement

/-! # Assembly of schemehood from compact affine etale images -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The compact local-image theorem used in the final affine chart reduction. -/
def AffineEtaleCompactImageRepresentability (S : Scheme.{u}) : Prop :=
  ∀ {B T V : Over S} [IsAffine B.left] [IsAffine T.left] [IsAffine V.left]
    (e : B ⟶ T) [Etale e.left] {F G : FppfSheaf S}
    {π : G.obj ⟶ F.obj} {p : G.obj ⟶ (schemeYoneda S).obj B}
    {f : F.obj ⟶ (schemeYoneda S).obj T} [Mono f]
    (_sq : IsPullback π p f ((schemeYoneda S).map e))
    (a : (schemeYoneda S).obj V ⟶ G.obj) (_haOpen : IsOpenImmersion a)
    (w : V ⟶ B) [LocallyOfFiniteType w.left]
    (_ha : a ≫ p = (schemeYoneda S).map w),
    CompactLocalImage.HasCompactRepresentation
      ((Subfunctor.range (a ≫ π)).sheafify (fppfTopology S))

private theorem localImage_comp_of_locallySurjective
    {S : Scheme.{u}} {F G H : Presheaf S}
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F)
    (q : G ⟶ H) (b : H ⟶ F)
    [CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) q] :
    (Subfunctor.range (q ≫ b)).sheafify (fppfTopology S) =
      (Subfunctor.range b).sheafify (fppfTopology S) := by
  apply le_antisymm
  · exact CompactLocalImage.localClosure_mono (Subfunctor.range_comp_le q b)
  · have hle : Subfunctor.range b ≤
        (Subfunctor.range (q ≫ b)).sheafify (fppfTopology S) := by
      rintro T x ⟨y, rfl⟩
      apply (fppfTopology S).superset_covering ?_
        (CategoryTheory.Presheaf.imageSieve_mem (fppfTopology S) q y)
      intro U f hf
      obtain ⟨z, hz⟩ := hf
      refine ⟨z, ?_⟩
      change b.app _ (q.app _ z) = F.map f.op (b.app T y)
      rw [hz, b.naturality_apply]
    exact (CompactLocalImage.localClosure_mono hle).trans_eq
      ((Subfunctor.range (q ≫ b)).sheafify_sheafify
        ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp hF))

/-- The affine open image of a finite chart supplies the open chart input
to the compact local-image theorem. -/
theorem EtaleAffineImageChart.hasRepresentedImage_of_affine_etale_compact_images
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    [IsAffine Y.left]
    {a : (schemeYoneda S).obj W ⟶ F.obj}
    {f : F.obj ⟶ (schemeYoneda S).obj Y} [Mono f] {x : W.left}
    (C : EtaleAffineImageChart F a f x)
    (himages : AffineEtaleCompactImageRepresentability S) :
    C.HasRepresentedImage := by
  let I := (Subfunctor.range C.chart).sheafify (fppfTopology S)
  obtain ⟨hI, V, hV, ⟨i⟩⟩ := C.imageAffine
  let : IsAffine V.left := hV
  let : IsAffine C.base.left := C.baseAffine
  let : Etale C.baseMap.left := C.baseEtale
  let : Mono C.toBase := C.square.mono_snd_of_mono
  let : _root_.AlgebraicGeometry.IsFinite C.finiteMap.left := C.finite
  obtain ⟨q, d, hq, hd, _, _, hde, hds, hqft, _⟩ :=
    representedLocalImageGeometry C.chart C.chartEtale C.toBase
      C.finiteMap C.chart_toBase i
  let b := i.hom ≫ I.ι
  have hb : IsOpenImmersion b := hI.iso_comp i
  have hbq : b ≫ C.toBase = (schemeYoneda S).map q := hq.symm
  let : LocallyOfFiniteType q.left := hqft
  have himage := himages C.baseMap C.square b hb q hbq
  let : Etale d.left := hde
  let : Surjective d.left := hds
  let : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      ((schemeYoneda S).map d) := isLocallySurjective_schemeYoneda_map d
  have hdc : (schemeYoneda S).map d ≫ (b ≫ C.toSpace) =
      C.chart ≫ C.toSpace := by
    dsimp [b]
    rw [← Category.assoc, ← Category.assoc, hd]
    rfl
  have heq := localImage_comp_of_locallySurjective F.property
    ((schemeYoneda S).map d) (b ≫ C.toSpace)
  rw [hdc] at heq
  obtain ⟨Z, _, hi⟩ := himage
  refine ⟨Z, ?_⟩
  rw [heq]
  exact hi

/-- Compact representability of affine etale local images finishes the
published monomorphism schemehood statement through point-lifted open charts. -/
theorem monomorphismLocallyFiniteTypeScheme_of_affine_etale_compact_images
    (himages : ∀ S : Scheme.{u}, AffineEtaleCompactImageRepresentability S) :
    MonomorphismLocallyFiniteTypeSchemeStatement.{u} := by
  intro S X Y f hf h
  obtain ⟨W, a, w, ha, hs, hw, hft⟩ := h
  let : Mono f := hf
  let : LocallyOfFiniteType w.left := hft
  apply exists_representation_of_affine_etale_images X.toSheaf a ha hs f w hw
  intro x N C
  let : IsAffine N.base.left := N.baseAffine
  let : Mono N.toBase := N.toBaseMono
  exact C.hasRepresentedImage_of_affine_etale_compact_images (himages S)

end Langlands.AlgebraicGeometry.AlgebraicSpace
