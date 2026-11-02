import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartClosedPointCoverage
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentableTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartGluingProof

/-! # Representability from scheme charts at closed atlas points -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k]
  {F : FppfSheaf (Spec (CommRingCat.of k))}
  {U : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType U.hom]

/-- A scheme chart around each closed atlas value suffices for representability.
The indexing set is the closed points of the atlas, in the scheme universe. -/
theorem representableBy_of_closed_point_charts
    (a : (schemeYoneda _).obj U ⟶ F.obj) (ha : IsEtale a) (hs : IsSurjective a)
    (hcharts : ∀ x : U.left, IsClosed ({x} : Set U.left) →
      ∃ (V : Over (Spec (CommRingCat.of k)))
        (b : (schemeYoneda _).obj V ⟶ F.obj),
        IsOpenImmersion b ∧
          F.obj.map (OpenSubfunctorPoints.residueFieldPoint U x).op
            (uliftYonedaEquiv a) ∈
              (Subfunctor.range b).obj
                (op (OpenSubfunctorPoints.residueFieldTest U x))) :
    ∃ P : Over (Spec (CommRingCat.of k)), Nonempty (F.obj.RepresentableBy P) := by
  classical
  let I := {x : U.left // IsClosed ({x} : Set U.left)}
  choose V b hb hc using (fun x : I => hcharts x.1 x.2)
  have hcov := OpenChartCoverage.isLocallySurjective_sigma_of_closed_residueField
    a ha hs b hb (fun x hx => ⟨⟨x, hx⟩, hc ⟨x, hx⟩⟩)
  obtain ⟨P, ⟨e⟩⟩ := openChartGluing _ F I V b hb hcov
  exact ⟨P, ⟨(Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} F.obj P).symm e⟩⟩

/-- The closed-point chart criterion also gives the separated, locally finite
type representer, conditional on the general fppf source-descent theorem. -/
theorem separated_lft_representableBy_of_closed_point_charts
    (hdesc : ∀ {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T),
      Surjective f → Flat f → LocallyOfFinitePresentation f →
        LocallyOfFiniteType (f ≫ g) → LocallyOfFiniteType g)
    (hd : IsClosedImmersion (Limits.diag F.obj))
    (a : (schemeYoneda _).obj U ⟶ F.obj) (ha : IsEtale a) (hs : IsSurjective a)
    (hcharts : ∀ x : U.left, IsClosed ({x} : Set U.left) →
      ∃ (V : Over (Spec (CommRingCat.of k)))
        (b : (schemeYoneda _).obj V ⟶ F.obj),
        IsOpenImmersion b ∧
          F.obj.map (OpenSubfunctorPoints.residueFieldPoint U x).op
            (uliftYonedaEquiv a) ∈
              (Subfunctor.range b).obj
                (op (OpenSubfunctorPoints.residueFieldTest U x))) :
    ∃ P : Over (Spec (CommRingCat.of k)),
      IsSeparated P.hom ∧ LocallyOfFiniteType P.hom ∧
        Nonempty (F.obj.RepresentableBy P) := by
  obtain ⟨P, ⟨e⟩⟩ := representableBy_of_closed_point_charts a ha hs hcharts
  exact ⟨P, isSeparated_of_representableBy e hd,
    locallyOfFiniteType_of_representableBy_of_sourceDescent
      hdesc e a ha hs inferInstance, ⟨e⟩⟩

/-- Closed-point charts locally of finite type give a separated locally finite
    type representer by Zariski locality on the actual glued scheme. -/
theorem separated_lft_representableBy_of_closed_point_lft_charts
    (hd : IsClosedImmersion (Limits.diag F.obj))
    (a : (schemeYoneda _).obj U ⟶ F.obj) (ha : IsEtale a) (hs : IsSurjective a)
    (hcharts : ∀ x : U.left, IsClosed ({x} : Set U.left) →
      ∃ (V : Over (Spec (CommRingCat.of k)))
        (b : (schemeYoneda _).obj V ⟶ F.obj),
        IsOpenImmersion b ∧ LocallyOfFiniteType V.hom ∧
          F.obj.map (OpenSubfunctorPoints.residueFieldPoint U x).op
            (uliftYonedaEquiv a) ∈
              (Subfunctor.range b).obj
                (op (OpenSubfunctorPoints.residueFieldTest U x))) :
    ∃ P : Over (Spec (CommRingCat.of k)),
      IsSeparated P.hom ∧ LocallyOfFiniteType P.hom ∧
        Nonempty (F.obj.RepresentableBy P) := by
  classical
  let I := {x : U.left // IsClosed ({x} : Set U.left)}
  choose V b hb hV hc using (fun x : I => hcharts x.1 x.2)
  have hcov := OpenChartCoverage.isLocallySurjective_sigma_of_closed_residueField
    a ha hs b hb (fun x hx => ⟨⟨x, hx⟩, hc ⟨x, hx⟩⟩)
  let P := SliceOpenGluing.glued hb
  let eIso : (schemeYoneda _).obj P ≅ F.obj :=
    (sheafToPresheaf _ _).mapIso (SliceOpenGluing.yonedaIsoSheaf hb)
  let e : F.obj.RepresentableBy P :=
    (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} F.obj P).symm eIso
  refine ⟨P, isSeparated_of_representableBy e hd, ?_, ⟨e⟩⟩
  change LocallyOfFiniteType (SliceOpenGluing.structureMap hb)
  apply IsZariskiLocalAtSource.of_openCover (SliceOpenGluing.schemeData hb).openCover
  intro i
  change LocallyOfFiniteType
    ((SliceOpenGluing.schemeData hb).ι i ≫ SliceOpenGluing.structureMap hb)
  rw [SliceOpenGluing.ι_structureMap]
  exact hV i

end Langlands.AlgebraicGeometry.AlgebraicSpace
