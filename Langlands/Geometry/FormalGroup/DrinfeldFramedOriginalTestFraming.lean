import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChangeFrameNaturality
import Langlands.Geometry.FormalGroup.DrinfeldFramedRestrictedTestSquare

/-! # Actual original normalized and refined framings on restricted tests -/

noncomputable section

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.QuasiIsogeny

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- The original-chart scalar transport is exactly the global actual quasi-isogeny transport. -/
theorem originalChartReAlgebra_eq_transport (f : QuasiIsogeny F E E' h)
    (S : CommAlgCat.{v} R) (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (C : CommAlgCat.{v} S) (b : Y.baseOpens S) (hb : IsUnit (algebraMap S C b.val)) :
    (letI := β;
      letI := coefficientAlgebra (O := O) C
      originalChartReAlgebra f S β e C b hb =
        ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra
          (α := coefficientAlgebra (O := O) (restrictTest S C))
          (letI := coefficientAlgebra (O := O) (restrictTest S C);
            f.onChart (restrictTest S C) (Y.baseSource S b) (Y.baseSource_unit S C b hb))
          (coefficientAlgebra (O := O) C) (coefficientAlgebra_comp_transport S C β e)) := by
  cases e
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

/-- Direct scalar transport of the specified original normalized framing on a restricted test. -/
def normalizedOriginalFramingOnRestrictedTest (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (a : X.target.val.reduction.atlas.opens)
    (ha : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) a.val)) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ)
    (letI := δ; X.chartFraming T a ha) γ eC

/-- Direct scalar transport of the specified actual further-refinement framing on the restricted test. -/
def refinedOriginalFramingOnRestrictedTest (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas) (a : q.opens)
    (ha : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) a.val)) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ)
    (letI := δ; X.refinedChartFraming q T a ha) γ eC

set_option backward.isDefEq.respectTransparency false in
/-- The original normalized map in the constructed base-change square is the same
actual original framing after scalar transport. -/
theorem baseChangeOriginalChartFraming_eq_transport (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    X.baseChangeOriginalChartFraming f C b hb =
      X.normalizedOriginalFramingOnRestrictedTest f C (X.baseChangeOriginalChart f b)
        (X.baseChangeOriginalChart_unit f C b hb) := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  let a := X.baseChangeOriginalChart f b
  let ha := X.baseChangeOriginalChart_unit f C b hb
  let oldGlobal := (letI := δ;
    BasicAtlas.globalOrderChartIso X.globalFrame.order a.val T ha)
  let oldRho := (letI := δ; X.rho.onChart T a ha)
  let _ := γ
  have hr := BasicAtlas.OrderAction.QuasiIsogeny.originalChartReAlgebra_eq_transport X.rho
    (BasicAtlas.coefficientTest φ) _ (BasicAtlas.coefficientAlgebraAlong_eq φ) C
    (X.baseChangeExtendedChart f b) hb
  have hs : X.normalizedOriginalFramingOnRestrictedTest f C a ha =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
        (oldGlobal.reAlgebra γ eC)).symm.trans
          (ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ) oldRho γ eC) := by
    change (ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra (α := δ)
      (letI := δ;
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) oldGlobal).symm.trans oldRho)
      γ eC) = _
    simp only [ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_trans,
      ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_symm,
      ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_ofIso]
  exact (congrArg (fun q =>
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K)
      (X.baseChangeOriginalGlobalChartIso f C b hb)).symm.trans q) hr).trans hs.symm

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
