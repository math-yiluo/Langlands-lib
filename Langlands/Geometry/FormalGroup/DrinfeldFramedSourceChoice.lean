import Langlands.Geometry.FormalGroup.DrinfeldFramedChartTransition
import Langlands.Geometry.FormalGroup.AtlasOrderRationalSourceChoice

/-! # Actual rational framing squares for changes of source-chart selection -/

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

/-- Actual normalized framings commute with changing the selected original chart. -/
theorem refinedChartFraming_sourceChoice (X : DrinfeldFramedAtlas Φ A)
    (q r : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (h : q.opens = r.opens)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : r.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    (X.refinedChartFraming q B
        (BasicAtlas.sourceChart (X := q.atlas) (Y := r.atlas) h b) hb).trans
      (q.orderSourceQuasi (F := K) X.target.val.reduction.order r h B b hb) =
        X.refinedChartFraming r B b hb := by
  let a := BasicAtlas.sourceChart (X := q.atlas) (Y := r.atlas) h b
  let iq := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (q.orderChartIso X.target.val.reduction.order B a hb)
  let ir := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (r.orderChartIso X.target.val.reduction.order B b hb)
  let tt := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (X.target.val.reduction.order.transitionIso B (q.source a) (r.source b)
      (q.source_unit B a hb) (r.source_unit B b hb))
  change ((X.chartFraming B (q.source a) (q.source_unit B a hb)).trans iq.symm).trans
      (iq.trans (tt.trans ir.symm)) =
    (X.chartFraming B (r.source b) (r.source_unit B b hb)).trans ir.symm
  calc
    ((X.chartFraming B (q.source a) (q.source_unit B a hb)).trans iq.symm).trans
        (iq.trans (tt.trans ir.symm)) =
      (X.chartFraming B (q.source a) (q.source_unit B a hb)).trans (tt.trans ir.symm) :=
        ModuleLaw.OrderAction.QuasiIsogeny.trans_symm_trans _ iq _
    _ = ((X.chartFraming B (q.source a) (q.source_unit B a hb)).trans tt).trans ir.symm :=
      (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _).symm
    _ = (X.chartFraming B (r.source b) (r.source_unit B b hb)).trans ir.symm :=
      congrArg (fun k => k.trans ir.symm)
        (X.chartFraming_transition B (q.source a) (r.source b)
          (q.source_unit B a hb) (r.source_unit B b hb))

/-- The square holds for the same actual source-choice atlas isomorphism used in joins. -/
theorem refinedChartFraming_sourceIso (X : DrinfeldFramedAtlas Φ A)
    (q r : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (h : q.opens = r.opens)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : r.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    (X.refinedChartFraming q B
        (BasicAtlas.sourceChart (X := q.atlas) (Y := r.atlas) h b) hb).trans
      ((BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
        (q.orderSourceIso X.target.val.reduction.order r h)).onChart B b hb) =
        X.refinedChartFraming r B b hb :=
  (congrArg (fun k => (X.refinedChartFraming q B
      (BasicAtlas.sourceChart (X := q.atlas) (Y := r.atlas) h b) hb).trans k)
    (q.orderSourceQuasi_eq_onChart (F := K) X.target.val.reduction.order r h B b hb).symm).trans
      (X.refinedChartFraming_sourceChoice q r h B b hb)

/-- The specified source-choice atlas comparison supplies an actual commuting framing square. -/
def sourceChoiceFramingSquare (X : DrinfeldFramedAtlas Φ A)
    (q r : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (h : q.opens = r.opens)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : r.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare (F := K)
      (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
      ((q.orderChart X.target.val.reduction.order
        (BasicAtlas.sourceChart (X := q.atlas) (Y := r.atlas) h b)).map
          (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb))
      ((r.orderChart X.target.val.reduction.order b).map
        (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb))
      (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B)) where
  top := X.refinedChartFraming q B
    (BasicAtlas.sourceChart (X := q.atlas) (Y := r.atlas) h b) hb
  right := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
    (q.orderSourceIso X.target.val.reduction.order r h)).onChart B b hb
  left := ModuleLaw.OrderAction.QuasiIsogeny.refl _
  bottom := X.refinedChartFraming r B b hb
  commutes := (X.refinedChartFraming_sourceIso q r h B b hb).trans
    (ModuleLaw.OrderAction.QuasiIsogeny.refl_trans _).symm

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
