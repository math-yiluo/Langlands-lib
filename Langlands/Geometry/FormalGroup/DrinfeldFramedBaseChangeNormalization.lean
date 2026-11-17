import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChangeCharts

/-! # Actual normalized framing square over a varying Nilp base -/

noncomputable section

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {E : OrderAction D M} {E' : OrderAction D N} {E'' : OrderAction D P}

/-- Rationalization retains composition of the actual integral full-order isomorphisms. -/
theorem ofIso_trans (a : Iso E E') (b : Iso E' E'') :
    ofIso (F := F) (a.trans b) = (ofIso a).trans (ofIso b) := by
  apply ext
  exact RationalHom.ofHom_comp b.hom a.hom

/-- Rationalization retains the actual inverse integral full-order map. -/
theorem ofIso_symm (a : Iso E E') :
    ofIso (F := F) a.symm = (ofIso a).symm := by
  apply ext
  rfl

section Normalization

variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ M₇ : ModuleLaw O R σ}
variable {E₀ : OrderAction D M₀} {E₁ : OrderAction D M₁}
variable {E₂ : OrderAction D M₂} {E₃ : OrderAction D M₃}
variable {E₄ : OrderAction D M₄} {E₅ : OrderAction D M₅}
variable {E₆ : OrderAction D M₆} {E₇ : OrderAction D M₇}

/-- Cancel the actual inverse corrections in the two normalized framing routes. -/
theorem normalization_transport (gn : QuasiIsogeny F E₁ E₀) (aa : QuasiIsogeny F E₂ E₁)
    (ss : QuasiIsogeny F E₂ E₃) (oo : QuasiIsogeny F E₃ E₄)
    (rr : QuasiIsogeny F E₃ E₅) (tt : QuasiIsogeny F E₇ E₆) (cc : QuasiIsogeny F E₆ E₅) :
    (gn.symm.trans ((aa.symm.trans (ss.trans (rr.trans cc.symm))).trans tt.symm)).trans
        (tt.trans cc) =
      (gn.symm.trans (aa.symm.trans (ss.trans oo))).trans (oo.symm.trans rr) := by
  simp only [trans_assoc]
  rw [← trans_assoc tt.symm tt cc, symm_trans_self, refl_trans]
  simp only [symm_trans_self, trans_refl]
  rw [← trans_assoc oo oo.symm rr, self_trans_symm, refl_trans]

end Normalization

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

/-- The original global normalization, transported to the new test scalar structure. -/
def baseChangeOriginalGlobalChartIso (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  (letI := coefficientAlgebra (O := 𝒪[K]) T;
    (BasicAtlas.globalOrderChartIso X.globalFrame.order (X.baseChangeOriginalChart f b).val T
      (X.baseChangeOriginalChart_unit f C b hb)).reAlgebra γ eC)

set_option backward.isDefEq.respectTransparency false in
/-- The same original rational chart framing, normalized after transport of the test scalars. -/
def baseChangeOriginalChartFraming (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :=
  letI := coefficientAlgebra (O := 𝒪[K]) C
  (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (X.baseChangeOriginalGlobalChartIso f C b hb)).symm.trans
      (BasicAtlas.OrderAction.QuasiIsogeny.originalChartReAlgebra X.rho
        (BasicAtlas.coefficientTest (Nilp.reducedScalarMap 𝒪[K] f)) _
        (BasicAtlas.coefficientAlgebraAlong_eq (Nilp.reducedScalarMap 𝒪[K] f)) C
        (X.baseChangeExtendedChart f b) hb)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The normalized extended framing commutes with the actual target and fixed-frame chart comparisons. -/
theorem chartFraming_baseChange (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    (letI := coefficientAlgebra (O := 𝒪[K]) C;
      ((X.baseChange f).chartFraming C b hb).trans
          (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (X.baseChangeTargetChartIso f C b hb)) =
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (X.baseChangeFrameChartIso f C b hb)).trans
          (X.baseChangeOriginalChartFraming f C b hb)) := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let _ := coefficientAlgebra (O := 𝒪[K]) C
  let gn := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (BasicAtlas.globalOrderChartIso (X.baseChange f).globalFrame.order b.val C hb)
  let aa := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    ((SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f).onChart C b hb)
  let ss := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (BasicAtlas.OrderAction.baseChangeAlongSourceOrderChartIso
      (Y := X.target.val.reduction.atlas) X.source.order φ rfl C (X.baseChangeExtendedChart f b) hb)
  let oo := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (X.baseChangeOriginalGlobalChartIso f C b hb)
  let rr := BasicAtlas.OrderAction.QuasiIsogeny.originalChartReAlgebra X.rho
    (BasicAtlas.coefficientTest φ) _ (BasicAtlas.coefficientAlgebraAlong_eq φ) C
    (X.baseChangeExtendedChart f b) hb
  let tt := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    ((X.target.val.reductionBaseChangeIso f).onChart C (X.baseChangeExtendedChart f b) hb)
  let cc := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
    (BasicAtlas.OrderAction.baseChangeAlongOrderChartIso X.target.val.reduction.order φ C
      (X.baseChangeExtendedChart f b) hb)
  have hr : (X.baseChange f).rho.onChart C b hb =
      (aa.symm.trans (ss.trans (rr.trans cc.symm))).trans tt.symm := by
    have h₁ := BasicAtlas.OrderAction.QuasiIsogeny.onChart_isoTransport
      (X.rho.baseChangeAlong φ)
      (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f)
      (X.target.val.reductionBaseChangeIso f).symm C b hb
    have h₂ := BasicAtlas.OrderAction.QuasiIsogeny.onChart_baseChangeAlong X.rho φ C
      (X.baseChangeExtendedChart f b) hb
    exact h₁.trans (congrArg (fun q => (aa.symm.trans q).trans tt.symm) h₂)
  have ht : ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (X.baseChangeTargetChartIso f C b hb) = tt.trans cc := by
    exact ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans
      ((X.target.val.reductionBaseChangeIso f).onChart C (X.baseChangeExtendedChart f b) hb)
      (BasicAtlas.OrderAction.baseChangeAlongOrderChartIso X.target.val.reduction.order φ C
        (X.baseChangeExtendedChart f b) hb)
  have hf : ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (X.baseChangeFrameChartIso f C b hb) = gn.symm.trans (aa.symm.trans (ss.trans oo)) := by
    simp only [baseChangeFrameChartIso, ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans,
      ModuleLaw.OrderAction.QuasiIsogeny.ofIso_symm]
    rfl
  have hl := congrArg₂ (fun q t => (gn.symm.trans q).trans t) hr ht
  have hs := congrArg (fun q => q.trans (oo.symm.trans rr)) hf
  exact hl.trans ((ModuleLaw.OrderAction.QuasiIsogeny.normalization_transport
    gn aa ss oo rr tt cc).trans hs.symm)

/-- The actual four full-order rational maps, with their proved normalized framing equation. -/
def baseChangeChartFramingSquare (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :=
  letI := coefficientAlgebra (O := 𝒪[K]) C
  ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.mk
    ((X.baseChange f).chartFraming C b hb)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (X.baseChangeTargetChartIso f C b hb))
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (X.baseChangeFrameChartIso f C b hb))
    (X.baseChangeOriginalChartFraming f C b hb) (X.chartFraming_baseChange f C b hb)

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
