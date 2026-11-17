import Langlands.Geometry.FormalGroup.DrinfeldFramedOriginalTestFraming

/-! # Actual base-change framing squares on arbitrary further refinements -/

noncomputable section

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ : Type} [Finite σ]
variable {M₀ M₁ M₂ M₃ M₄ M₅ : ModuleLaw O R σ}
variable {E₀ : OrderAction D M₀} {E₁ : OrderAction D M₁}
variable {E₂ : OrderAction D M₂} {E₃ : OrderAction D M₃}
variable {E₄ : OrderAction D M₄} {E₅ : OrderAction D M₅}

/-- An actual framing square extends across an inverse refinement correction and a target correction. -/
theorem refinement_transport (a : QuasiIsogeny F E₀ E₁) (b : QuasiIsogeny F E₁ E₂)
    (c : QuasiIsogeny F E₀ E₃) (d : QuasiIsogeny F E₃ E₂)
    (n : QuasiIsogeny F E₄ E₁) (r : QuasiIsogeny F E₂ E₅)
    (h : a.trans b = c.trans d) :
    (a.trans n.symm).trans (n.trans (b.trans r)) = c.trans (d.trans r) := by
  simp only [trans_assoc]
  rw [← trans_assoc n.symm n (b.trans r), symm_trans_self, refl_trans,
    ← trans_assoc a b r, h, trans_assoc]

end Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The specified original parent chart maps to the specified original further-refined chart. -/
def originalRefinedTargetTestIso (X : DrinfeldFramedAtlas Φ A)
    (T : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (a : X.target.val.reduction.atlas.opens)
    (ha : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj T a.val))
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas) (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj T b.val)) :=
  (X.target.val.reduction.order.transitionIso T a (q.source b) ha (q.source_unit T b hb)).trans
    (q.orderChartIso X.target.val.reduction.order T b hb).symm

/-- The actual original normalized framing reaches any specified further-refined chart. -/
theorem chartFraming_originalRefinedTargetTestIso (X : DrinfeldFramedAtlas Φ A)
    (T : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (a : X.target.val.reduction.atlas.opens)
    (ha : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj T a.val))
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas) (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj T b.val)) :
    (X.chartFraming T a ha).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (X.originalRefinedTargetTestIso T a ha q b hb)) =
      X.refinedChartFraming q T b hb := by
  let tr := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (X.target.val.reduction.order.transitionIso T a (q.source b) ha (q.source_unit T b hb))
  let qi := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (q.orderChartIso X.target.val.reduction.order T b hb)
  have ht := X.chartFraming_transition T a (q.source b) ha (q.source_unit T b hb)
  have hi : ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
      (X.originalRefinedTargetTestIso T a ha q b hb) = tr.trans qi.symm := by
    exact (ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans _ _).trans
      (congrArg (fun z => tr.trans z) (ModuleLaw.OrderAction.QuasiIsogeny.ofIso_symm _))
  exact (congrArg (fun z => (X.chartFraming T a ha).trans z) hi).trans
    ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _).symm.trans
      (congrArg (fun z => z.trans qi.symm) ht))

/-- The original target-chart correction, on the restricted test and at the new scalars. -/
def originalRefinedTargetOnRestrictedTestIso (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (a : X.target.val.reduction.atlas.opens)
    (ha : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) a.val))
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas) (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) b.val)) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  (letI := coefficientAlgebra (O := 𝒪[K]) T;
    (X.originalRefinedTargetTestIso T a ha q b hb).reAlgebra γ eC)

set_option backward.isDefEq.respectTransparency false in
/-- Directly transported original framings commute with the specified actual refined target correction. -/
theorem normalizedOriginalFraming_refinedTarget (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (a : X.target.val.reduction.atlas.opens)
    (ha : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) a.val))
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas) (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) b.val)) :
    (letI := coefficientAlgebra (O := 𝒪[K]) C;
      (X.normalizedOriginalFramingOnRestrictedTest f C a ha).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
          (X.originalRefinedTargetOnRestrictedTestIso f C a ha q b hb)) =
        X.refinedOriginalFramingOnRestrictedTest f C q b hb) := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  let n := (letI := δ; X.chartFraming T a ha)
  let r := (letI := δ; ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (X.originalRefinedTargetTestIso T a ha q b hb))
  have ho := (letI := δ; X.chartFraming_originalRefinedTargetTestIso T a ha q b hb)
  have h := congrArg (fun z => ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ) z γ eC) ho
  have ht := ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_trans (α := δ) n r γ eC
  have hr := ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_ofIso (F := K) (α := δ)
    (letI := δ; X.originalRefinedTargetTestIso T a ha q b hb) γ eC
  let _ := γ
  exact ((congrArg (fun z =>
    (ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ) n γ eC).trans z) hr).symm.trans
      ht.symm).trans h

set_option backward.isDefEq.respectTransparency false in
/-- Actual integral target comparison between any specified new and original refined charts. -/
def baseChangeRefinedTargetTestIso (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (q : BasicAtlas.CoverRefinement (X.baseChange f).target.val.reduction.atlas) (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val))
    (r : BasicAtlas.CoverRefinement X.target.val.reduction.atlas) (a : r.opens)
    (ha : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) a.val)) :=
  letI := coefficientAlgebra (O := 𝒪[K]) C
  let p := q.source b
  let hp := q.source_unit C b hb
  (q.orderChartIso (X.baseChange f).target.val.reduction.order C b hb).trans
    ((X.baseChangeTargetChartIso f C p hp).trans
      (X.originalRefinedTargetOnRestrictedTestIso f C (X.baseChangeOriginalChart f p)
        (X.baseChangeOriginalChart_unit f C p hp) r a ha))

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical base-change framing square holds on any specified new and old refinements. -/
theorem refinedChartFraming_baseChange (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (q : BasicAtlas.CoverRefinement (X.baseChange f).target.val.reduction.atlas) (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val))
    (r : BasicAtlas.CoverRefinement X.target.val.reduction.atlas) (a : r.opens)
    (ha : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) a.val)) :
    (letI := coefficientAlgebra (O := 𝒪[K]) C;
      ((X.baseChange f).refinedChartFraming q C b hb).trans
          (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
            (X.baseChangeRefinedTargetTestIso f C q b hb r a ha)) =
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
          (X.baseChangeGlobalFrameTestIso f C)).trans
            (X.refinedOriginalFramingOnRestrictedTest f C r a ha)) := by
  let _ := coefficientAlgebra (O := 𝒪[K]) C
  let p := q.source b
  let hp := q.source_unit C b hb
  let o := X.baseChangeOriginalChart f p
  let ho := X.baseChangeOriginalChart_unit f C p hp
  let nf := (X.baseChange f).chartFraming C p hp
  let ni := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (q.orderChartIso (X.baseChange f).target.val.reduction.order C b hb)
  let ti := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (X.baseChangeTargetChartIso f C p hp)
  let oi := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (X.originalRefinedTargetOnRestrictedTestIso f C o ho r a ha)
  let fi := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (X.baseChangeGlobalFrameTestIso f C)
  let ofr := X.normalizedOriginalFramingOnRestrictedTest f C o ho
  have hc : nf.trans ti = fi.trans ofr :=
    (X.chartFraming_baseChange_canonical f C p hp).trans
      (congrArg (fun z => fi.trans z) (X.baseChangeOriginalChartFraming_eq_transport f C p hp))
  have hi : ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (X.baseChangeRefinedTargetTestIso f C q b hb r a ha) = ni.trans (ti.trans oi) := by
    exact (ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans _ _).trans
      (congrArg (fun z => ni.trans z) (ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans _ _))
  have hr := X.normalizedOriginalFraming_refinedTarget f C o ho r a ha
  exact (congrArg (fun z => ((X.baseChange f).refinedChartFraming q C b hb).trans z) hi).trans
    ((ModuleLaw.OrderAction.QuasiIsogeny.refinement_transport nf ti fi ofr ni oi hc).trans
      (congrArg (fun z => fi.trans z) hr))

/-- Four specified actual maps with the proved further-refinement base-change framing equation. -/
def baseChangeRefinedFramingSquare (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (q : BasicAtlas.CoverRefinement (X.baseChange f).target.val.reduction.atlas) (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val))
    (r : BasicAtlas.CoverRefinement X.target.val.reduction.atlas) (a : r.opens)
    (ha : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) a.val)) :=
  letI := coefficientAlgebra (O := 𝒪[K]) C
  ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.mk
    ((X.baseChange f).refinedChartFraming q C b hb)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (X.baseChangeRefinedTargetTestIso f C q b hb r a ha))
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (X.baseChangeGlobalFrameTestIso f C))
    (X.refinedOriginalFramingOnRestrictedTest f C r a ha)
    (X.refinedChartFraming_baseChange f C q b hb r a ha)

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
