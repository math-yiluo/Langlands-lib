import Langlands.Geometry.FormalGroup.DrinfeldFramedReducedComposition

/-! # Transport of actual reduced framing squares through source changes -/

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

set_option backward.isDefEq.respectTransparency false in
/-- An actual source-choice square transports the complete rational framing square. -/
theorem ReducedFramingSquare.of_source_square (e : X.residueMap = Y.residueMap)
    (c d : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (hL : c.left.opens = d.left.opens) (hR : c.right.opens = d.right.opens)
    (hs : (c.left.orderSourceIso X.target.val.reduction.order d.left hL).trans d.coordinateIso =
      c.coordinateIso.trans (c.right.orderSourceIso Y.target.val.reduction.order d.right hR))
    (hc : ReducedFramingSquare e c) : ReducedFramingSquare e d := by
  intro B b hb
  let a := BasicAtlas.sourceChart (X := c.right.atlas) (Y := d.right.atlas) hR b
  let fl := X.refinedChartFraming c.left B
    (BasicAtlas.sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a) hb
  let fr := Y.refinedChartFraming c.right B a hb
  let gl := X.refinedChartFraming d.left B
    (BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b) hb
  let gr := Y.refinedChartFraming d.right B b hb
  let sl := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
    (c.left.orderSourceIso X.target.val.reduction.order d.left hL)).onChart B
      (BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b) hb
  let sr := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
    (c.right.orderSourceIso Y.target.val.reduction.order d.right hR)).onChart B b hb
  let fi := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
  have hl : fl.trans sl = gl := X.refinedChartFraming_sourceIso c.left d.left hL B
    (BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b) hb
  have hr : fr.trans sr = gr := Y.refinedChartFraming_sourceIso c.right d.right hR B b hb
  have ho : fl.trans (reducedComparisonOnChart c B a hb) = fi.trans fr := hc B a hb
  have ht := congrArg (fun f => (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) f).onChart B b hb) hs
  simp only [BasicAtlas.OrderAction.QuasiIsogeny.ofIso_trans,
    BasicAtlas.OrderAction.QuasiIsogeny.onChart_trans] at ht
  change sl.trans (reducedComparisonOnChart d B b hb) =
    (reducedComparisonOnChart c B a hb).trans sr at ht
  change gl.trans (reducedComparisonOnChart d B b hb) = fi.trans gr
  exact (congrArg (fun k => k.trans (reducedComparisonOnChart d B b hb)) hl.symm).trans
    ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fl sl _).trans
      ((congrArg (fun k => fl.trans k) ht).trans
        ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fl _ sr).symm.trans
          ((congrArg (fun k => k.trans sr) ho).trans
            ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fi fr sr).trans
              (congrArg (fun k => fi.trans k) hr))))))

/-- Retain the specified comparison together with its transported rational framing square. -/
def sourceTransportedReducedComparison (e : X.residueMap = Y.residueMap)
    (c d : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (hL : c.left.opens = d.left.opens) (hR : c.right.opens = d.right.opens)
    (hs : (c.left.orderSourceIso X.target.val.reduction.order d.left hL).trans d.coordinateIso =
      c.coordinateIso.trans (c.right.orderSourceIso Y.target.val.reduction.order d.right hR))
    (hc : ReducedFramingSquare e c) :
    {f : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction //
      ReducedFramingSquare e f} :=
  ⟨d, ReducedFramingSquare.of_source_square e c d hL hR hs hc⟩

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
