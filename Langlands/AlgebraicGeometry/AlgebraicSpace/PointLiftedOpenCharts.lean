import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartCoverage
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartGluingProof

/-! # Scheme representability from point lifts into open charts -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Each atlas point lifts to a scheme mapping compatibly into an open
scheme chart of the target. The lifting map need not be etale. -/
def HasPointLiftedOpenCharts {S : Scheme.{u}} {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) : Prop :=
  ∀ x : U.left, ∃ (V D : Over S) (b : (schemeYoneda S).obj V ⟶ F)
    (j : D ⟶ U) (c : D ⟶ V) (d : D.left),
    IsOpenImmersion b ∧
      (schemeYoneda S).map j ≫ a = (schemeYoneda S).map c ≫ b ∧
      j.left d = x

/-- An open subfunctor containing a lifted point also contains the
residue-field value of the original point. -/
theorem mem_residueField_of_point_lift
    {S : Scheme.{u}} {F : Presheaf S} {A : Subfunctor F}
    (hA : IsOpenImmersion A.ι) {U D : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (j : D ⟶ U)
    (b : (schemeYoneda S).obj D ⟶ A.toFunctor)
    (h : b ≫ A.ι = (schemeYoneda S).map j ≫ a)
    (d : D.left) (x : U.left) (hd : j.left d = x) :
    F.map (OpenSubfunctorPoints.residueFieldPoint U x).op (uliftYonedaEquiv a) ∈
      A.obj (op (OpenSubfunctorPoints.residueFieldTest U x)) := by
  let l := hA.rep.lift b j h
  have hl : l ≫ hA.rep.snd a = j :=
    Functor.relativelyRepresentable.lift_snd _ _ _ _
  rw [OpenSubfunctorPoints.mem_map_iff_range_subset hA,
    Equiv.symm_apply_apply]
  rintro y ⟨z, rfl⟩
  change U.left.fromSpecResidueField x z ∈ Set.range (hA.rep.snd a).left
  rw [U.left.fromSpecResidueField_apply x z, ← hd]
  exact ⟨l.left d, congrArg (fun k : D ⟶ U => k.left d) hl⟩

/-- Point-lifted open charts around every point of an etale surjective
atlas yield a scheme representing the fppf sheaf. -/
theorem exists_representation_of_point_lifted_open_charts
    {S : Scheme.{u}} (F : FppfSheaf S) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F.obj) (ha : IsEtale a) (hs : IsSurjective a)
    (hcharts : HasPointLiftedOpenCharts a) :
    ∃ V : Over S, Nonempty ((schemeYoneda S).obj V ≅ F.obj) := by
  classical
  choose V D b j c d hb hcomm hd using hcharts
  have hcov := OpenChartCoverage.isLocallySurjective_sigma_of_residueField a ha hs b hb
    (fun x => ⟨x, mem_residueField_of_point_lift
      (OpenSubfunctorLifting.range_open (b x) (hb x)) a (j x)
      ((schemeYoneda S).map (c x) ≫ Subfunctor.toRange (b x))
      (by rw [Category.assoc, Subfunctor.toRange_ι]; exact (hcomm x).symm)
      (d x) x (hd x)⟩)
  exact openChartGluing S F U.left V b hb hcov

end Langlands.AlgebraicGeometry.AlgebraicSpace
