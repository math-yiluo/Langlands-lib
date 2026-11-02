import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineAtlasNeighborhoods
import Langlands.AlgebraicGeometry.AlgebraicSpace.PointLiftedOpenCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers

/-! # Reduction of schemehood to images of affine etale charts -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The image in the original sheaf of a finite affine chart after an
etale base change is represented by an actual scheme. -/
def EtaleAffineImageChart.HasRepresentedImage
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    {a : (schemeYoneda S).obj W ⟶ F.obj}
    {f : F.obj ⟶ (schemeYoneda S).obj Y} {x : W.left}
    (C : EtaleAffineImageChart F a f x) : Prop :=
  ∃ V : Over S, Nonempty ((schemeYoneda S).obj V ≅
    ((Subfunctor.range (C.chart ≫ C.toSpace)).sheafify (fppfTopology S)).toFunctor)

/-- A represented image in an affine target neighborhood gives an
open scheme chart of the original sheaf with a compatible point lift. -/
theorem AffineAtlasNeighborhood.pointLift_of_representedImage
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    {a : (schemeYoneda S).obj W ⟶ F.obj}
    {f : F.obj ⟶ (schemeYoneda S).obj Y} {x : W.left}
    (N : AffineAtlasNeighborhood F a f x)
    (C : EtaleAffineImageChart N.sheaf N.chart N.toBase N.point)
    (hC : C.HasRepresentedImage) :
    ∃ (V D : Over S) (b : (schemeYoneda S).obj V ⟶ F.obj)
      (j : D ⟶ W) (c : D ⟶ V) (d : D.left),
      IsOpenImmersion b ∧
        (schemeYoneda S).map j ≫ a = (schemeYoneda S).map c ≫ b ∧
        j.left d = x := by
  obtain ⟨V, ⟨e⟩⟩ := hC
  let q := C.chart ≫ C.toSpace
  let Q := (Subfunctor.range q).sheafify (fppfTopology S)
  have hπ : IsEtale C.toSpace := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
        (schemeYoneda S)) C.square.flip (isEtale_map C.baseMap C.baseEtale)
  have hQ : IsOpenImmersion Q.ι :=
    OpenSubfunctorImages.sheafify_range_open q (C.chartEtale.comp hπ)
  let b := e.hom ≫ Q.ι ≫ N.toSpace
  let c : C.source ⟶ V := (schemeYoneda S).preimage
    (Subfunctor.toRangeSheafify (fppfTopology S) q ≫ e.inv)
  have hc : (schemeYoneda S).map c ≫ b = q ≫ N.toSpace := by
    dsimp [c, b]
    rw [Functor.map_preimage, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc]
    rfl
  have hj : (schemeYoneda S).map (C.toAtlas ≫ N.toAtlas) ≫ a =
      q ≫ N.toSpace := by
    dsimp [q]
    rw [C.chart_toSpace, Category.assoc, N.chart_toSpace,
      Functor.map_comp, Category.assoc]
  refine ⟨V, C.source, b, C.toAtlas ≫ N.toAtlas, c, C.point,
    (hQ.iso_comp e).comp' N.toSpaceOpen, hj.trans hc.symm, ?_⟩
  change N.toAtlas.left (C.toAtlas.left C.point) = x
  rw [C.point_eq, N.point_eq]

/-- The unresolved image representability step, applied to the affine
local data, supplies all point-lifted open charts. -/
theorem hasPointLiftedOpenCharts_of_affine_etale_images
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    (a : (schemeYoneda S).obj W ⟶ F.obj) (ha : IsEtale a)
    (f : F.obj ⟶ (schemeYoneda S).obj Y) [Mono f]
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w)
    [LocallyOfFiniteType w.left]
    (himages : ∀ (x : W.left) (N : AffineAtlasNeighborhood F a f x)
      (C : EtaleAffineImageChart N.sheaf N.chart N.toBase N.point),
      C.HasRepresentedImage) :
    HasPointLiftedOpenCharts a := by
  intro x
  obtain ⟨N⟩ := nonempty_affineAtlasNeighborhood a ha f w hw x
  obtain ⟨C⟩ := N.nonempty_etaleAffineImageChart
  exact N.pointLift_of_representedImage C (himages x N C)

/-- Once the indicated etale images are represented, the original
surjective atlas glues to an actual scheme representer. -/
theorem exists_representation_of_affine_etale_images
    {S : Scheme.{u}} (F : FppfSheaf S) {W Y : Over S}
    (a : (schemeYoneda S).obj W ⟶ F.obj) (ha : IsEtale a) (hs : IsSurjective a)
    (f : F.obj ⟶ (schemeYoneda S).obj Y) [Mono f]
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w)
    [LocallyOfFiniteType w.left]
    (himages : ∀ (x : W.left) (N : AffineAtlasNeighborhood F a f x)
      (C : EtaleAffineImageChart N.sheaf N.chart N.toBase N.point),
      C.HasRepresentedImage) :
    ∃ V : Over S, Nonempty ((schemeYoneda S).obj V ≅ F.obj) :=
  exists_representation_of_point_lifted_open_charts F a ha hs
    (hasPointLiftedOpenCharts_of_affine_etale_images a ha f w hw himages)

end Langlands.AlgebraicGeometry.AlgebraicSpace
