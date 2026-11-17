import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChangeTargetSquare

/-! # Exact edges of the actual framed base-change target square -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas.Comparison

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual original reduced comparison chart map at the new test scalar structure. -/
def baseChangeOriginalReducedTestComparison (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ)
    (letI := δ; reducedComparisonOnChart (SpecialAtlas.reductionComparison c.targetComparison) T
      (c.baseChangeOriginalReducedChart f b) (c.baseChangeOriginalReducedChart_unit f C b hb)) γ eC

set_option backward.isDefEq.respectTransparency false in
/-- The pasted top edge is the same specified actual new reduced comparison map. -/
theorem baseChangePastedTargetSquare_top (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    (c.baseChangePastedTargetSquare f C b hb).top =
      reducedComparisonOnChart (X := X.baseChange f) (Y := Y.baseChange f)
        (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)) C b hb := by
  exact (BasicAtlas.OrderAction.QuasiIsogeny.onChart_ofIso
    (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).coordinateIso C b hb).symm

set_option backward.isDefEq.respectTransparency false in
/-- The pasted bottom edge is the same specified actual old reduced comparison map after scalar transport. -/
theorem baseChangePastedTargetSquare_bottom (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    (c.baseChangePastedTargetSquare f C b hb).bottom =
      c.baseChangeOriginalReducedTestComparison f C b hb := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  let o := SpecialAtlas.reductionComparison c.targetComparison
  let a := c.baseChangeOriginalReducedChart f b
  let ha := c.baseChangeOriginalReducedChart_unit f C b hb
  let n := SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)
  let bl := BasicAtlas.sourceChart (X := n.left.atlas) (Y := n.right.atlas) n.sameCover b
  let xn := n.left.source bl
  let yn := n.right.source b
  let hxn := n.left.source_unit C bl hb
  let hyn := n.right.source_unit C b hb
  let xo := X.baseChangeOriginalChart f xn
  let yo := Y.baseChangeOriginalChart f yn
  let hxo := X.baseChangeOriginalChart_unit f C xn hxn
  let hyo := Y.baseChangeOriginalChart_unit f C yn hyn
  have hp := ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.reAlgebra_bottom (α := δ)
    (letI := δ; o.refinementTestSquare (F := K) T a ha xo yo hxo hyo) γ eC
  have hi := (letI := δ; BasicAtlas.OrderAction.QuasiIsogeny.onChart_ofIso (F := K)
    o.coordinateIso T a ha)
  exact hp.trans (congrArg (fun z => ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ) z γ eC) hi.symm)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The pasted right edge is exactly the actual target correction in the further-refinement framing square. -/
theorem baseChangePastedTargetSquare_right (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    (let n := SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)
      let o := SpecialAtlas.reductionComparison c.targetComparison
      let a := c.baseChangeOriginalReducedChart f b
      let ha := c.baseChangeOriginalReducedChart_unit f C b hb
      letI := coefficientAlgebra (O := 𝒪[K]) C
      (c.baseChangePastedTargetSquare f C b hb).right =
        ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
          (Y.baseChangeRefinedTargetTestIso f C n.right b hb o.right a ha)) := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  let n := SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)
  let o := SpecialAtlas.reductionComparison c.targetComparison
  let a := c.baseChangeOriginalReducedChart f b
  let ha := c.baseChangeOriginalReducedChart_unit f C b hb
  let bl := BasicAtlas.sourceChart (X := n.left.atlas) (Y := n.right.atlas) n.sameCover b
  let xn := n.left.source bl
  let yn := n.right.source b
  let hxn := n.left.source_unit C bl hb
  let hyn := n.right.source_unit C b hb
  let xo := X.baseChangeOriginalChart f xn
  let yo := Y.baseChangeOriginalChart f yn
  let hxo := X.baseChangeOriginalChart_unit f C xn hxn
  let hyo := Y.baseChangeOriginalChart_unit f C yn hyn
  let _ := γ
  let pn := n.right.parentOrderTestIso (Y.baseChange f).target.val.reduction.order C yn hyn b hb
  let po := (letI := δ; o.right.parentOrderTestIso Y.target.val.reduction.order T yo hyo a ha)
  let qt := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    ((Y.target.val.reductionBaseChangeIso f).onChart C (Y.baseChangeExtendedChart f yn) hyn)
  let cc := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (BasicAtlas.OrderAction.baseChangeAlongOrderChartIso Y.target.val.reduction.order φ C
      (Y.baseChangeExtendedChart f yn) hyn)
  let nr := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (n.right.orderChartIso (Y.baseChange f).target.val.reduction.order C b hb)
  let rr := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (Y.originalRefinedTargetOnRestrictedTestIso f C yo hyo o.right a ha)
  let so := ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.reAlgebra (α := δ)
    (letI := δ; o.refinementTestSquare (F := K) T a ha xo yo hxo hyo) γ eC
  have hp := ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.reAlgebra_right (α := δ)
    (letI := δ; o.refinementTestSquare (F := K) T a ha xo yo hxo hyo) γ eC
  have ho : ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.right (O := 𝒪[K]) (R := C) so = rr :=
    hp.trans (ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_ofIso (α := δ) (F := K) po γ eC)
  have hn : (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K) pn).symm = nr :=
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso_symm pn).symm.trans
      (congrArg (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K))
        (n.right.parentOrderTestIso_at_source (Y.baseChange f).target.val.reduction.order C b hb))
  have hc := congrArg₂ (fun z w => ((z.trans qt).trans cc).trans w) hn ho
  have ht : ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (Y.baseChangeRefinedTargetTestIso f C n.right b hb o.right a ha) =
        nr.trans (qt.trans (cc.trans rr)) := by
    simp only [baseChangeRefinedTargetTestIso, baseChangeTargetChartIso,
      ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans, ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc]
    rfl
  exact hc.trans ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc (nr.trans qt) cc rr).trans
    ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc nr qt (cc.trans rr)).trans ht.symm))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The pasted left edge is exactly the actual target correction in the further-refinement framing square. -/
theorem baseChangePastedTargetSquare_left (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    (let n := SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)
      let o := SpecialAtlas.reductionComparison c.targetComparison
      let a := c.baseChangeOriginalReducedChart f b
      let ha := c.baseChangeOriginalReducedChart_unit f C b hb
      let bl := BasicAtlas.sourceChart (X := n.left.atlas) (Y := n.right.atlas) n.sameCover b
      let al := BasicAtlas.sourceChart (X := o.left.atlas) (Y := o.right.atlas) o.sameCover a
      letI := coefficientAlgebra (O := 𝒪[K]) C
      (c.baseChangePastedTargetSquare f C b hb).left =
        ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
          (X.baseChangeRefinedTargetTestIso f C n.left bl hb o.left al ha)) := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  let n := SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)
  let o := SpecialAtlas.reductionComparison c.targetComparison
  let a := c.baseChangeOriginalReducedChart f b
  let ha := c.baseChangeOriginalReducedChart_unit f C b hb
  let al := BasicAtlas.sourceChart (X := o.left.atlas) (Y := o.right.atlas) o.sameCover a
  let bl := BasicAtlas.sourceChart (X := n.left.atlas) (Y := n.right.atlas) n.sameCover b
  let xn := n.left.source bl
  let yn := n.right.source b
  let hxn := n.left.source_unit C bl hb
  let hyn := n.right.source_unit C b hb
  let xo := X.baseChangeOriginalChart f xn
  let yo := Y.baseChangeOriginalChart f yn
  let hxo := X.baseChangeOriginalChart_unit f C xn hxn
  let hyo := Y.baseChangeOriginalChart_unit f C yn hyn
  let _ := γ
  let pn := n.left.parentOrderTestIso (X.baseChange f).target.val.reduction.order C xn hxn bl hb
  let po := (letI := δ; o.left.parentOrderTestIso X.target.val.reduction.order T xo hxo al ha)
  let qt := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    ((X.target.val.reductionBaseChangeIso f).onChart C (X.baseChangeExtendedChart f xn) hxn)
  let cc := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (BasicAtlas.OrderAction.baseChangeAlongOrderChartIso X.target.val.reduction.order φ C
      (X.baseChangeExtendedChart f xn) hxn)
  let nr := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (n.left.orderChartIso (X.baseChange f).target.val.reduction.order C bl hb)
  let rr := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (X.originalRefinedTargetOnRestrictedTestIso f C xo hxo o.left al ha)
  let so := ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.reAlgebra (α := δ)
    (letI := δ; o.refinementTestSquare (F := K) T a ha xo yo hxo hyo) γ eC
  have hp := ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.reAlgebra_left (α := δ)
    (letI := δ; o.refinementTestSquare (F := K) T a ha xo yo hxo hyo) γ eC
  have ho : ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.left (O := 𝒪[K]) (R := C) so = rr :=
    hp.trans (ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_ofIso (α := δ) (F := K) po γ eC)
  have hn : (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K) pn).symm = nr :=
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso_symm pn).symm.trans
      (congrArg (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K))
        (n.left.parentOrderTestIso_at_source (X.baseChange f).target.val.reduction.order C bl hb))
  have hc := congrArg₂ (fun z w => ((z.trans qt).trans cc).trans w) hn ho
  have ht : ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (X.baseChangeRefinedTargetTestIso f C n.left bl hb o.left al ha) =
        nr.trans (qt.trans (cc.trans rr)) := by
    simp only [baseChangeRefinedTargetTestIso, baseChangeTargetChartIso,
      ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans, ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc]
    rfl
  exact hc.trans ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc (nr.trans qt) cc rr).trans
    ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc nr qt (cc.trans rr)).trans ht.symm))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual refined target square has exactly the two comparison maps and two framing corrections. -/
def baseChangeTargetSquare (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    c.BaseChangeTargetSquare f C b hb :=
  let n := SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)
  let o := SpecialAtlas.reductionComparison c.targetComparison
  let a := c.baseChangeOriginalReducedChart f b
  let ha := c.baseChangeOriginalReducedChart_unit f C b hb
  let bl := BasicAtlas.sourceChart (X := n.left.atlas) (Y := n.right.atlas) n.sameCover b
  let al := BasicAtlas.sourceChart (X := o.left.atlas) (Y := o.right.atlas) o.sameCover a
  letI := coefficientAlgebra (O := 𝒪[K]) C
  ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.mk
    (reducedComparisonOnChart (X := X.baseChange f) (Y := Y.baseChange f) n C b hb)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (Y.baseChangeRefinedTargetTestIso f C n.right b hb o.right a ha))
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (X.baseChangeRefinedTargetTestIso f C n.left bl hb o.left al ha))
    (c.baseChangeOriginalReducedTestComparison f C b hb) (by
      let sq := c.baseChangePastedTargetSquare f C b hb
      have ht := c.baseChangePastedTargetSquare_top f C b hb
      have hr := c.baseChangePastedTargetSquare_right f C b hb
      have hl := c.baseChangePastedTargetSquare_left f C b hb
      have hb' := c.baseChangePastedTargetSquare_bottom f C b hb
      exact (congrArg₂ ModuleLaw.OrderAction.QuasiIsogeny.trans ht hr).symm.trans
        (sq.commutes.trans (congrArg₂ ModuleLaw.OrderAction.QuasiIsogeny.trans hl hb')))

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas.Comparison
