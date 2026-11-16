import Langlands.Geometry.FormalGroup.AtlasRationalHeight
import Langlands.Geometry.FormalGroup.RationalHeightIso
import Langlands.Geometry.FormalGroup.AtlasOrderRationalRefinement

/-! # Actual local rational heights on finer principal covers -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.RationalHom.HasConstantChartHeight

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {h : X.opens = Y.opens}
variable {f : BasicAtlas.RationalHom F X Y h} {π : O} {q : ℕ} {n : ℤ}

/-- The actual rational restriction retains the same local kernel-rank difference. -/
theorem restrictCover (hf : f.HasConstantChartHeight π q n) (r : CoverRefinement X) :
    (BasicAtlas.RationalHom.restrict (Y := Y) (h := h) r f).HasConstantChartHeight π q n := by
  intro A b hb
  change r.opens at b
  rw [BasicAtlas.RationalHom.onChart_restrict]
  have ht := (hf A (sourceChart h.symm (r.source b)) (r.source_unit A b hb)).ofGlobal_isoTransport
    (r.chartIso A b hb).symm ((r.retarget Y h).chartIso A b hb).symm
  have he := ModuleLaw.RationalHom.isoTransport_eq_comp
    (r.chartIso A b hb).symm ((r.retarget Y h).chartIso A b hb).symm
    (BasicAtlas.RationalHom.onChart (X := X) (Y := Y) (h := h)
      A (sourceChart h.symm (r.source b)) (r.source_unit A b hb) f)
  exact (congrArg
    (fun z => RationalSection.HasHeightFunction π q (RationalSection.ofGlobal z) (fun _ => n))
    he).mp ht

/-- Actual scalar divisibility on the original chart transports through the same
formal coordinate comparisons, giving the refined framing's genuine local map. -/
def refinedLocalQuasiIsogeny (hf : f.HasConstantChartHeight π q n)
    (r : CoverRefinement X) (hπ : algebraMap O F π ≠ 0)
    (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (hX : ((X.chart (r.source b)).map
      (coefficientLift (O := O) (r.source b).val A (r.source_unit A b hb))).IsPiDivisible π)
    (hY : ((Y.chart (sourceChart h.symm (r.source b))).map
      (coefficientLift (O := O) (r.source b).val A (r.source_unit A b hb))).IsPiDivisible π) :
    LocalQuasiIsogeny F π
      ((r.atlas.chart b).map (coefficientLift (O := O) b.val A hb))
      (((r.retarget Y h).atlas.chart b).map (coefficientLift (O := O) b.val A hb)) ⊤ :=
  (hf.restrictCover r).localQuasiIsogeny hπ A b hb
    ((r.chartIso A b hb).symm.isPiDivisible π hX)
    (((r.retarget Y h).chartIso A b hb).symm.isPiDivisible π hY)

@[simp]
theorem refinedLocalQuasiIsogeny_val (hf : f.HasConstantChartHeight π q n)
    (r : CoverRefinement X) (hπ : algebraMap O F π ≠ 0)
    (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (hX : ((X.chart (r.source b)).map
      (coefficientLift (O := O) (r.source b).val A (r.source_unit A b hb))).IsPiDivisible π)
    (hY : ((Y.chart (sourceChart h.symm (r.source b))).map
      (coefficientLift (O := O) (r.source b).val A (r.source_unit A b hb))).IsPiDivisible π) :
    (hf.refinedLocalQuasiIsogeny r hπ A b hb hX hY).val =
      RationalSection.ofGlobal
        (BasicAtlas.RationalHom.onChart
          (X := r.atlas) (Y := (r.retarget Y h).atlas)
          (h := r.opens_eq_retarget (Y := Y) (h := h)) A b hb
          (BasicAtlas.RationalHom.restrict (Y := Y) (h := h) r f)) := rfl

/-- The genuine refined local map retains the prescribed height. -/
theorem refinedLocalQuasiIsogeny_height (hf : f.HasConstantChartHeight π q n)
    (r : CoverRefinement X) (hπ : algebraMap O F π ≠ 0)
    (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (hX : ((X.chart (r.source b)).map
      (coefficientLift (O := O) (r.source b).val A (r.source_unit A b hb))).IsPiDivisible π)
    (hY : ((Y.chart (sourceChart h.symm (r.source b))).map
      (coefficientLift (O := O) (r.source b).val A (r.source_unit A b hb))).IsPiDivisible π) :
    RationalSection.HasHeightFunction π q
      (hf.refinedLocalQuasiIsogeny r hπ A b hb hX hY).val (fun _ => n) :=
  hf.restrictCover r A b hb

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.RationalHom.HasConstantChartHeight
