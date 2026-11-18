import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.IsomorphismSchemeBaseChange

/-! # Difference of cocycles in an inner form -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S S' : Scheme.{u}} {G : GroupScheme S} {U : Over S}

/-- An inner form with local coordinates in which transport from `a` to `b` is
conjugation by the inverse of `ξ(a,b)`. -/
structure InnerTwist (ξ : Cocycle G U) where
  obj : GroupScheme S
  chart : LocalGroupIso obj G U
  transition : ∀ {Z : Over S} (a b : Z ⟶ U) (g : Z ⟶ obj.X),
    chart.toFun b g = (ξ.toFun a b)⁻¹ * chart.toFun a g * ξ.toFun a b

namespace InnerTwist

variable {ξ : Cocycle G U} (D : InnerTwist ξ)

theorem chart_reverse {Z : Over S} (a b : Z ⟶ U) (g : Z ⟶ D.obj.X) :
    D.chart.toFun a g = ξ.toFun a b * D.chart.toFun b g * (ξ.toFun a b)⁻¹ := by
  rw [D.transition a b]
  group

/-- The difference `ζ(a,b) ξ(a,b)⁻¹` in the chart at `a` is a cocycle of the inner form. -/
def difference (ζ : Cocycle G U) : Cocycle D.obj U where
  toFun a b := (D.chart.toFun a).symm (ζ.toFun a b * (ξ.toFun a b)⁻¹)
  naturality t a b := by
    have h := D.chart.symm.naturality t a (ζ.toFun a b * (ξ.toFun a b)⁻¹)
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← ζ.naturality, ← ξ.naturality] at h
    exact h
  cocycle a b c := by
    apply (D.chart.toFun a).injective
    rw [(D.chart.toFun a).map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      D.chart_reverse a b ((D.chart.toFun b).symm _), MulEquiv.apply_symm_apply,
      ζ.cocycle a b c, ξ.cocycle a b c]
    group

theorem chart_difference (ζ : Cocycle G U) {Z : Over S} (a b : Z ⟶ U) :
    D.chart.toFun a ((D.difference ζ).toFun a b) = ζ.toFun a b * (ξ.toFun a b)⁻¹ :=
  (D.chart.toFun a).apply_symm_apply _

private theorem chart_cochain (g : U ⟶ D.obj.X) {Z : Over S} (a : Z ⟶ U) :
    D.chart.toFun a (a ≫ g) = a ≫ D.chart.toFun (𝟙 U) g := by
  simpa only [Category.comp_id] using D.chart.naturality a (𝟙 U) g

/-- Pairwise cohomology is triviality of the difference in the inner form. -/
theorem cohomologous_iff_difference_isTrivial (ζ : Cocycle G U) :
    ξ.Cohomologous ζ ↔ (D.difference ζ).IsTrivial := by
  constructor
  · rintro ⟨f, hf⟩
    let g := (D.chart.toFun (𝟙 U)).symm f⁻¹
    have hg : D.chart.toFun (𝟙 U) g = f⁻¹ := (D.chart.toFun (𝟙 U)).apply_symm_apply _
    refine ⟨g, fun a b => ?_⟩
    apply (D.chart.toFun a).injective
    rw [D.chart_difference, map_mul, map_inv, D.chart_cochain g a,
      D.chart_reverse a b (b ≫ g), D.chart_cochain g b, hg, GrpObj.comp_inv, GrpObj.comp_inv,
      hf a b]
    change (a ≫ f)⁻¹ * ξ.toFun a b * (b ≫ f) * (ξ.toFun a b)⁻¹ = _
    group
  · rintro ⟨g, hg⟩
    let f := (D.chart.toFun (𝟙 U) g)⁻¹
    refine ⟨f, fun a b => ?_⟩
    have key := congrArg (D.chart.toFun a) (hg a b)
    rw [D.chart_difference, map_mul, map_inv, D.chart_cochain g a,
      D.chart_reverse a b (b ≫ g), D.chart_cochain g b] at key
    calc
      ζ.toFun a b = (ζ.toFun a b * (ξ.toFun a b)⁻¹) * ξ.toFun a b := by group
      _ = (ξ.twist f).toFun a b := by
        rw [key]
        simp only [Cocycle.twist, f, GrpObj.comp_inv]
        group

/-- The chart and its inner transitions are preserved by arbitrary base change. -/
def baseChange (b : S' ⟶ S) (V : Over S') (r : (Over.map b).obj V ⟶ U) :
    InnerTwist (ξ.baseChange b V r) where
  obj := (GroupScheme.baseChange b).obj D.obj
  chart := (D.chart.refine r).baseChangeFamily b
  transition {Z} a c g := by
    apply (baseChangePointsEquiv b G Z).injective
    simp only [LocalGroupIso.baseChangeFamily_toFun, LocalGroupIso.refine_toFun,
      map_mul, map_inv, Cocycle.baseChange_toFun]
    exact D.transition _ _ _

private theorem chart_baseChange (b : S' ⟶ S) (V : Over S') (r : (Over.map b).obj V ⟶ U)
    {Z : Over S'} (a : Z ⟶ V) (g : Z ⟶ (D.baseChange b V r).obj.X) :
    baseChangePointsEquiv b G Z ((D.baseChange b V r).chart.toFun a g) =
      D.chart.toFun ((Over.map b).map a ≫ r) (baseChangePointsEquiv b D.obj Z g) :=
  LocalGroupIso.baseChangeFamily_toFun b (D.chart.refine r) a g

/-- Taking the difference in the inner form commutes with base change on each test. -/
theorem baseChange_difference_toFun (ζ : Cocycle G U) (b : S' ⟶ S)
    (V : Over S') (r : (Over.map b).obj V ⟶ U) {Z : Over S'} (a c : Z ⟶ V) :
    ((D.difference ζ).baseChange b V r).toFun a c =
      ((D.baseChange b V r).difference (ζ.baseChange b V r)).toFun a c := by
  apply (baseChangePointsEquiv b D.obj Z).injective
  apply (D.chart.toFun ((Over.map b).map a ≫ r)).injective
  rw [Cocycle.baseChange_toFun, D.chart_difference, ← D.chart_baseChange b V r,
    InnerTwist.chart_difference, map_mul, map_inv, Cocycle.baseChange_toFun, Cocycle.baseChange_toFun]

/-- A cohomology relation after base change makes the base-changed difference trivial. -/
theorem baseChange_difference_isTrivial (ζ : Cocycle G U) (b : S' ⟶ S)
    (V : Over S') (r : (Over.map b).obj V ⟶ U)
    (h : (ξ.baseChange b V r).Cohomologous (ζ.baseChange b V r)) :
    ((D.difference ζ).baseChange b V r).IsTrivial := by
  obtain ⟨f, hf⟩ := ((D.baseChange b V r).cohomologous_iff_difference_isTrivial _).mp h
  exact ⟨f, fun a c => (D.baseChange_difference_toFun ζ b V r a c).trans (hf a c)⟩

end InnerTwist
end Langlands.GroupScheme.Cocycle
