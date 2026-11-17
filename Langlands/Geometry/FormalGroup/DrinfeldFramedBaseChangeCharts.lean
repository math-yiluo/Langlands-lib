import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChange
import Langlands.Geometry.FormalGroup.DrinfeldFramedChartTransition
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlongCharts

/-! # Actual fixed-frame and target chart comparisons over a new Nilp base -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.QuasiIsogeny

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {X' : BasicAtlas O R υ} {Y' : BasicAtlas O R ω}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {G : OrderAction D X'} {G' : OrderAction D Y'}
variable {h : X.opens = Y.opens} {aCover : X.opens = X'.opens}
variable {bCover : Y.opens = Y'.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Restriction of the actual rationalized isomorphism is the rationalized actual chart isomorphism. -/
theorem onChart_ofIso (f : Iso E E' h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (ofIso (F := F) f).onChart A b hb =
      ModuleLaw.OrderAction.QuasiIsogeny.ofIso (f.onChart A b hb) := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual chart map of an isomorphism-transported atlas quasi-isogeny. -/
theorem onChart_isoTransport (f : QuasiIsogeny F E E' h)
    (a : Iso E G aCover) (b : Iso E' G' bCover)
    (A : CommAlgCat.{v} R) (c : Y'.opens) (hc : IsUnit (algebraMap R A c.val)) :
    (f.isoTransport a b).onChart A c hc =
      ((ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F)
        (a.onChart A (sourceChart (X := X') (Y := Y')
          ((aCover.symm.trans h).trans bCover) c) hc)).symm.trans
          (f.onChart A (sourceChart (X := Y) (Y := Y') bCover c) hc)).trans
            (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (b.onChart A c hc)) := by
  rw [isoTransport, onChart_trans, onChart_trans]
  simp only [← ofIso_symm, onChart_ofIso]
  rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.QuasiIsogeny

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

/-- The extended original quotient chart identified by the actual quotient-square cover equality. -/
def baseChangeExtendedChart (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (b : (X.baseChange f).target.val.reduction.atlas.opens) :
    (X.target.val.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)).atlas.opens :=
  BasicAtlas.sourceChart
    (X := (X.target.val.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)).atlas)
    (Y := (X.baseChange f).target.val.reduction.atlas)
    (X.target.val.atlas.reductionBaseChangeOpens_eq f).symm b

/-- The actual original reduced target chart selected under the induced quotient map. -/
def baseChangeOriginalChart (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (b : (X.baseChange f).target.val.reduction.atlas.opens) : X.target.val.reduction.atlas.opens :=
  X.target.val.reduction.atlas.baseSource (BasicAtlas.coefficientTest (Nilp.reducedScalarMap 𝒪[K] f))
    (X.baseChangeExtendedChart f b)

/-- Unit evidence for the same selected original chart on the restricted test algebra. -/
theorem baseChangeOriginalChart_unit (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C)
      (X.baseChangeOriginalChart f b).val) :=
  X.target.val.reduction.atlas.baseSource_unit
    (BasicAtlas.coefficientTest (Nilp.reducedScalarMap 𝒪[K] f)) C
    (X.baseChangeExtendedChart f b) hb

/-- Actual full-order target test-chart comparison through quotient naturality and supplied scalars. -/
def baseChangeTargetChartIso (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :=
  letI := coefficientAlgebra (O := 𝒪[K]) C
  ((X.target.val.reductionBaseChangeIso f).onChart C (X.baseChangeExtendedChart f b) hb).trans
    (BasicAtlas.OrderAction.baseChangeAlongOrderChartIso X.target.val.reduction.order
      (Nilp.reducedScalarMap 𝒪[K] f) C (X.baseChangeExtendedChart f b) hb)

/-- Actual full-order fixed-frame test comparison through exactly the source maps used by baseChange. -/
def baseChangeFrameChartIso (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  letI := γ
  let i₁ := (BasicAtlas.globalOrderChartIso (X.baseChange f).globalFrame.order b.val C hb).symm
  let i₂ := (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f).onChart C b hb
  let i₃ := BasicAtlas.OrderAction.baseChangeAlongSourceOrderChartIso
    (Y := X.target.val.reduction.atlas) X.source.order φ rfl C (X.baseChangeExtendedChart f b) hb
  let i₄ := (letI := coefficientAlgebra (O := 𝒪[K]) T
    (BasicAtlas.globalOrderChartIso X.globalFrame.order (X.baseChangeOriginalChart f b).val T
      (X.baseChangeOriginalChart_unit f C b hb)).reAlgebra γ eC)
  i₁.trans (i₂.symm.trans (i₃.trans i₄))

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
