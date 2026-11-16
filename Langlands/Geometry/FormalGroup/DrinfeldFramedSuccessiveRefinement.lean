import Langlands.Geometry.FormalGroup.DrinfeldFramedChartTransition
import Langlands.Geometry.FormalGroup.AtlasOrderRationalRefinementComposition

/-! # Actual framing squares for successive principal-cover refinements -/

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

/-- Apply the actual normalized framing and then the second refined-chart identification. -/
def successiveRefinedFraming (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (r : BasicAtlas.CoverRefinement q.atlas)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : r.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny K
      (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
      ((r.orderChart (q.orderAction X.target.val.reduction.order) b).map
        (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb)) :=
  (X.refinedChartFraming q B (r.source b) (r.source_unit B b hb)).trans
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
      (r.orderChartIso (q.orderAction X.target.val.reduction.order) B b hb)).symm

/-- The actual direct-to-successive formal comparison identifies the two rational framing routes. -/
theorem refinedChartFraming_comp (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (r : BasicAtlas.CoverRefinement q.atlas)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : r.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    (X.refinedChartFraming (q.comp r) B b hb).trans
        (q.orderCompQuasi (F := K) X.target.val.reduction.order r B b hb) =
      X.successiveRefinedFraming q r B b hb := by
  let iq := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (q.orderChartIso X.target.val.reduction.order B (r.source b) (r.source_unit B b hb))
  let ir := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (r.orderChartIso (q.orderAction X.target.val.reduction.order) B b hb)
  let idr := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    ((q.comp r).orderChartIso X.target.val.reduction.order B b hb)
  let cq := q.orderCompQuasi (F := K) X.target.val.reduction.order r B b hb
  let f := X.chartFraming B (q.source (r.source b))
    (q.source_unit B (r.source b) (r.source_unit B b hb))
  have he : cq.trans (ir.trans iq) = idr :=
    (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc cq ir iq).symm.trans
      (q.orderCompQuasi_chart (F := K) X.target.val.reduction.order r B b hb)
  have hi : idr.symm.trans cq = iq.symm.trans ir.symm :=
    ModuleLaw.OrderAction.QuasiIsogeny.symm_trans_of_trans_eq cq (ir.trans iq) idr he
  change (f.trans idr.symm).trans cq = (f.trans iq.symm).trans ir.symm
  calc
    (f.trans idr.symm).trans cq = f.trans (idr.symm.trans cq) :=
      ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _
    _ = f.trans (iq.symm.trans ir.symm) := congrArg (fun k => f.trans k) hi
    _ = (f.trans iq.symm).trans ir.symm :=
      (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _).symm

/-- Actual square data for the specified direct-to-successive refinement comparison. -/
def successiveRefinementFramingSquare (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (r : BasicAtlas.CoverRefinement q.atlas)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : r.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare (F := K)
      (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
      (((q.comp r).orderChart X.target.val.reduction.order b).map
        (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb))
      ((r.orderChart (q.orderAction X.target.val.reduction.order) b).map
        (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb))
      (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B)) where
  top := X.refinedChartFraming (q.comp r) B b hb
  right := q.orderCompQuasi (F := K) X.target.val.reduction.order r B b hb
  left := ModuleLaw.OrderAction.QuasiIsogeny.refl _
  bottom := X.successiveRefinedFraming q r B b hb
  commutes := (X.refinedChartFraming_comp q r B b hb).trans
    (ModuleLaw.OrderAction.QuasiIsogeny.refl_trans _).symm

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
