import Langlands.Geometry.FormalGroup.DrinfeldFramedComparison
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderTransition

/-! # Actual normalized framing and its formal chart-transition equation -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Normalize the source of the actual framing to the globally extended fixed frame. -/
def chartFraming (X : DrinfeldFramedAtlas Φ A)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : X.target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny K
      (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
      ((X.target.val.reduction.order.chart b).map
        (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb)) :=
  (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
    (BasicAtlas.globalOrderChartIso X.globalFrame.order b.val B hb)).symm.trans
      (X.rho.onChart B b hb)

/-- The previous arbitrary-refinement framing is this chart normalization
followed by the inverse actual refined-chart identification. -/
theorem refinedChartFraming_eq_chartFraming (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    X.refinedChartFraming q B b hb =
      (X.chartFraming B (q.source b) (q.source_unit B b hb)).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
          (q.orderChartIso X.target.val.reduction.order B b hb)).symm := rfl

/-- Changing the actual reduced target chart transports the same normalized rational framing. -/
theorem chartFraming_transition (X : DrinfeldFramedAtlas Φ A)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b c : X.target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val))
    (hc : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B c.val)) :
    (X.chartFraming B b hb).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
          (X.target.val.reduction.order.transitionIso B b c hb hc)) =
      X.chartFraming B c hc := by
  let gb := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (BasicAtlas.globalOrderChartIso X.globalFrame.order b.val B hb)
  let gc := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (BasicAtlas.globalOrderChartIso X.globalFrame.order c.val B hc)
  let st := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (X.source.order.transitionIso B b c hb hc)
  let tt := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (X.target.val.reduction.order.transitionIso B b c hb hc)
  have hr : (X.rho.onChart B b hb).trans tt = st.trans (X.rho.onChart B c hc) :=
    BasicAtlas.OrderAction.QuasiIsogeny.onChart_transition X.rho B b c hb hc
  have hg : gb.symm.trans st = gc.symm :=
    BasicAtlas.globalOrderChartQuasi_transition X.globalFrame.order
      X.target.val.reduction.atlas.opens X.target.val.reduction.atlas.covers B b c hb hc
  change (gb.symm.trans (X.rho.onChart B b hb)).trans tt =
    gc.symm.trans (X.rho.onChart B c hc)
  calc
    (gb.symm.trans (X.rho.onChart B b hb)).trans tt =
        gb.symm.trans ((X.rho.onChart B b hb).trans tt) :=
      ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _
    _ = gb.symm.trans (st.trans (X.rho.onChart B c hc)) :=
      congrArg (fun k => gb.symm.trans k) hr
    _ = (gb.symm.trans st).trans (X.rho.onChart B c hc) :=
      (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _).symm
    _ = gc.symm.trans (X.rho.onChart B c hc) :=
      congrArg (fun k => k.trans (X.rho.onChart B c hc)) hg

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
