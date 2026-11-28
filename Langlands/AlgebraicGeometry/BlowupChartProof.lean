import Langlands.AlgebraicGeometry.BlowupChartStatement
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.FiniteDegree.ChartProbe
import WeilConjectures.Blowup.Proper

/-! # Blow-ups with a chart at a global section of the centre: proof -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The Library's dilatation algebra `A[I/a]` is the chart algebra of the affine blow-up. -/
theorem coordinateAlgebra_eq_chartRing {A : Type u} [CommRing A] (a : A) (I : Ideal A) :
    GroupScheme.Dilatation.coordinateAlgebra a I = AffineBlowup.chartRing I a := by
  have h : ∀ x : A, GroupScheme.Dilatation.divided a x = AffineBlowup.chartFraction a 1 x := by
    intro x
    apply (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).mul_left_cancel
    rw [GroupScheme.Dilatation.mul_divided, AffineBlowup.chartFraction, Localization.mk_eq_mk']
    simp
  unfold GroupScheme.Dilatation.coordinateAlgebra AffineBlowup.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (h x).symm⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, h x⟩

theorem blowupChartStatement : BlowupChartStatement.{u} := by
  intro X _ t I ht
  refine ⟨I.blowup, I.blowupMap, inferInstance, I.isIso_blowupMap_restrict_support_compl, ?_⟩
  intro U
  have ha : X.presheaf.map (homOfLE le_top).op t ∈ I.ideal U := ht U
  let e := (AffineBlowup.homogeneousAwayEquivChart (I.ideal U) ha).trans
    (Subalgebra.equivOfEq _ _
      (coordinateAlgebra_eq_chartRing (X.presheaf.map (homOfLE le_top).op t)
        (I.ideal U)).symm).toRingEquiv
  refine ⟨Spec.map e.toCommRingCatIso.hom ≫ I.blowupChart U ha, inferInstance, ?_⟩
  rw [Category.assoc, I.blowupChart_comp_blowupMap, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  have h1 := AffineBlowup.homogeneousAwayToChart_awayAlgebraMap (I.ideal U) ha r
  have h2 := congrArg Subtype.val h1
  exact h2

end Langlands.AlgebraicGeometry
