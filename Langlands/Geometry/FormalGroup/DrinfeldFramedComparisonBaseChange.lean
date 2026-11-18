import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChangeTargetEdges

/-! # Actual original framed comparisons under Nilp-base extension -/

noncomputable section

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ : Type} [Finite σ]
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ M₇ : ModuleLaw O R σ}
variable {E₀ : OrderAction D M₀} {E₁ : OrderAction D M₁}
variable {E₂ : OrderAction D M₂} {E₃ : OrderAction D M₃}
variable {E₄ : OrderAction D M₄} {E₅ : OrderAction D M₅}
variable {E₆ : OrderAction D M₆} {E₇ : OrderAction D M₇}

/-- Five actual comparison squares transport a framing equation through both fixed-frame and target maps. -/
theorem framing_transport
    {x : QuasiIsogeny F E₀ E₁} {y : QuasiIsogeny F E₃ E₂}
    {t : QuasiIsogeny F E₁ E₂} {n : QuasiIsogeny F E₀ E₃}
    {cx : QuasiIsogeny F E₁ E₄} {cy : QuasiIsogeny F E₂ E₅}
    {fx : QuasiIsogeny F E₀ E₆} {fy : QuasiIsogeny F E₃ E₇}
    {xo : QuasiIsogeny F E₆ E₄} {yo : QuasiIsogeny F E₇ E₅}
    {co : QuasiIsogeny F E₄ E₅} {fo : QuasiIsogeny F E₆ E₇}
    (hx : x.trans cx = fx.trans xo) (hy : y.trans cy = fy.trans yo)
    (ht : t.trans cy = cx.trans co) (ho : xo.trans co = fo.trans yo)
    (hf : n.trans fy = fx.trans fo) : x.trans t = n.trans y := by
  apply trans_right_cancel (x.trans t) (n.trans y) cy
  calc
    (x.trans t).trans cy = x.trans (t.trans cy) := trans_assoc _ _ _
    _ = x.trans (cx.trans co) := congrArg (fun q => x.trans q) ht
    _ = (x.trans cx).trans co := (trans_assoc _ _ _).symm
    _ = (fx.trans xo).trans co := congrArg (fun q => q.trans co) hx
    _ = fx.trans (xo.trans co) := trans_assoc _ _ _
    _ = fx.trans (fo.trans yo) := congrArg (fun q => fx.trans q) ho
    _ = (fx.trans fo).trans yo := (trans_assoc _ _ _).symm
    _ = (n.trans fy).trans yo := congrArg (fun q => q.trans yo) hf.symm
    _ = n.trans (fy.trans yo) := trans_assoc _ _ _
    _ = n.trans (y.trans cy) := congrArg (fun q => n.trans q) hy.symm
    _ = (n.trans y).trans cy := (trans_assoc _ _ _).symm

end Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny

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

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The specified actual original framing square survives Nilp-base extension. -/
theorem framingSquare_baseChange (c : Comparison X Y) (f : A ⟶ B) :
    FramingSquare (baseChange_residue_eq c.residue_eq f) (c.baseChangedTargetComparison f) := by
  intro C b hb
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
  let al := BasicAtlas.sourceChart (X := o.left.atlas) (Y := o.right.atlas) o.sameCover a
  let _ := γ
  have hx := X.refinedChartFraming_baseChange f C n.left bl hb o.left al ha
  have hy := Y.refinedChartFraming_baseChange f C n.right b hb o.right a ha
  have ht := (c.baseChangeTargetSquare f C b hb).commutes
  have hf := (baseChangeResidueFrameSquare c.residue_eq f C).commutes
  have ho' := congrArg (fun q => ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ) q γ eC)
    (letI := δ; c.square T a ha)
  have ho : (X.refinedOriginalFramingOnRestrictedTest f C o.left al ha).trans
      (c.baseChangeOriginalReducedTestComparison f C b hb) =
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (baseChangeResidueFrameTestIso c.residue_eq f C)).trans
        (Y.refinedOriginalFramingOnRestrictedTest f C o.right a ha) := by
    let oldx := (letI := δ; X.refinedChartFraming o.left T al ha)
    let oldt := (letI := δ; reducedComparisonOnChart o T a ha)
    let oldy := (letI := δ; Y.refinedChartFraming o.right T a ha)
    let oldi := (letI := δ; (globalFrameIso c.residue_eq).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj T))
    let oldq := (letI := δ; ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) oldi)
    have hxt := ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_trans (α := δ) oldx oldt γ eC
    have hyt := ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_trans (α := δ) oldq oldy γ eC
    have hit := ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_ofIso (α := δ) (F := K) oldi γ eC
    exact hxt.symm.trans (ho'.trans (hyt.trans
      (congrArg (fun z => z.trans (ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ) oldy γ eC)) hit)))
  exact ModuleLaw.OrderAction.QuasiIsogeny.framing_transport hx hy ht ho hf

/-- Extend the specified original framed comparison, retaining its target formal comparison and framing certificate. -/
def baseChange (c : Comparison X Y) (f : A ⟶ B) : Comparison (X.baseChange f) (Y.baseChange f) where
  targetComparison := c.baseChangedTargetComparison f
  residue_eq := baseChange_residue_eq c.residue_eq f
  square := c.framingSquare_baseChange f

@[simp]
theorem baseChange_targetComparison (c : Comparison X Y) (f : A ⟶ B) :
    (c.baseChange f).targetComparison =
      SpecialAtlas.baseChangeAlongComparison c.targetComparison (Nilp.scalarMap 𝒪[K] f) := rfl

@[simp]
theorem baseChange_residue (c : Comparison X Y) (f : A ⟶ B) :
    (c.baseChange f).residue_eq = baseChange_residue_eq c.residue_eq f := rfl

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas.Comparison
