import Langlands.Geometry.FormalGroup.DrinfeldFramedSuccessiveRefinement
import Langlands.Geometry.FormalGroup.AtlasOrderComparisonRefinementChart

/-! # Actual preservation of reduced framing squares under further refinement -/

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
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The direct refined framing followed by the actual route to the selected old finer chart
equals the original normalized framing on that chart. -/
theorem refinedChartFraming_comp_to_old (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (r : BasicAtlas.CoverRefinement q.atlas)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : r.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    (X.refinedChartFraming (q.comp r) B b hb).trans
      ((q.orderCompQuasi (F := K) X.target.val.reduction.order r B b hb).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
          (r.orderChartIso (q.orderAction X.target.val.reduction.order) B b hb))) =
      X.refinedChartFraming q B (r.source b) (r.source_unit B b hb) := by
  let cp := q.orderCompQuasi (F := K) X.target.val.reduction.order r B b hb
  let ic := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (r.orderChartIso (q.orderAction X.target.val.reduction.order) B b hb)
  let fn := X.refinedChartFraming (q.comp r) B b hb
  let fo := X.refinedChartFraming q B (r.source b) (r.source_unit B b hb)
  have he : fn.trans cp = fo.trans ic.symm := X.refinedChartFraming_comp q r B b hb
  exact (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fn cp ic).symm.trans
    ((congrArg (fun k => k.trans ic) he).trans
      ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fo ic.symm ic).trans
        ((congrArg (fun k => fo.trans k)
          (ModuleLaw.OrderAction.QuasiIsogeny.symm_trans_self ic)).trans
            (ModuleLaw.OrderAction.QuasiIsogeny.trans_refl fo))))

/-- A specified actual reduced framing square survives any further principal refinement. -/
theorem ReducedFramingSquare.refine (e : X.residueMap = Y.residueMap)
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (h : ReducedFramingSquare e c) (q : BasicAtlas.CoverRefinement c.left.atlas) :
    ReducedFramingSquare e (c.refine q) := by
  intro B b hb
  change q.opens at b
  let r := q.retarget c.right.atlas c.sameCover
  let a := BasicAtlas.sourceChart (X := c.right.atlas) (Y := c.left.atlas)
    c.sameCover.symm (q.source b)
  let S := BasicAtlas.OrderAction.Comparison.refinementChartSquare
    (F := K) c q B b hb
  let fl := X.refinedChartFraming (c.left.comp q) B b hb
  let fr := Y.refinedChartFraming (c.right.comp r) B b hb
  let ol := X.refinedChartFraming c.left B (q.source b) (q.source_unit B b hb)
  let orr := Y.refinedChartFraming c.right B a (q.source_unit B b hb)
  let fi := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
  have hl : fl.trans S.left = ol := X.refinedChartFraming_comp_to_old c.left q B b hb
  have hr : fr.trans S.right = orr := Y.refinedChartFraming_comp_to_old c.right r B b hb
  have ho : ol.trans S.bottom = fi.trans orr := h B a (q.source_unit B b hb)
  change fl.trans S.top = fi.trans fr
  apply ModuleLaw.OrderAction.QuasiIsogeny.trans_right_cancel _ _ S.right
  exact (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fl S.top S.right).trans
    ((congrArg (fun k => fl.trans k) S.commutes).trans
      ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fl S.left S.bottom).symm.trans
        ((congrArg (fun k => k.trans S.bottom) hl).trans
          (ho.trans ((congrArg (fun k => fi.trans k) hr.symm).trans
            (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fi fr S.right).symm)))))

/-- Actual square data after refining a specified reduced framing comparison. -/
def refinedReducedFramingSquare (e : X.residueMap = Y.residueMap)
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (h : ReducedFramingSquare e c) (q : BasicAtlas.CoverRefinement c.left.atlas)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : (c.refine q).right.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare (F := K)
      (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
      (((c.refine q).left.orderChart X.target.val.reduction.order
        (BasicAtlas.sourceChart (X := (c.refine q).left.atlas) (Y := (c.refine q).right.atlas)
          (c.refine q).sameCover b)).map
            (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb))
      (((c.refine q).right.orderChart Y.target.val.reduction.order b).map
        (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb))
      (Y.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B)) where
  top := X.refinedChartFraming (c.refine q).left B
    (BasicAtlas.sourceChart (X := (c.refine q).left.atlas) (Y := (c.refine q).right.atlas)
      (c.refine q).sameCover b) hb
  right := reducedComparisonOnChart (c.refine q) B b hb
  left := ModuleLaw.OrderAction.QuasiIsogeny.ofIso
    ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
  bottom := Y.refinedChartFraming (c.refine q).right B b hb
  commutes := ReducedFramingSquare.refine e c h q B b hb

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
