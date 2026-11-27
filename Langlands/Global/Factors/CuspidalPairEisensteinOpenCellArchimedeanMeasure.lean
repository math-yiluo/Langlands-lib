import Langlands.Global.Factors.CuspidalPairEisensteinArchimedeanNumeratorStatement
import Langlands.Global.IntegralFiniteAdeles
import Langlands.Global.AdelesSecondCountable

/-! # The archimedean image of the open-cell Haar measure on a finite region

Let `R` be an open set of adelic `(t + 1) × (r + 1)` matrices containing `0`, stable under
adding matrices with vanishing finite components, and contained in the matrices with integral
finite components. The image of the restriction of `openCellHaar` to `R` under the
archimedean projection `Y ↦ Y_∞` is a nonzero constant multiple of the archimedean Haar measure
`archimedeanOpenCellHaar` (uniqueness of Haar measure), so integrals of functions of `Y_∞`
over `R` are a nonzero constant times archimedean integrals. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.CuspidalPairEisenstein.ArchimedeanMeasure

open MeasureTheory NumberField
open scoped NNReal ENNReal

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

variable (F r t) in
/-- The archimedean component `Y_∞` of an adelic matrix `Y`. -/
def archimedeanPart (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F) :=
  fun i j => (Y i j).1

theorem continuous_archimedeanPart : Continuous (archimedeanPart F r t) :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_fst.comp ((continuous_apply j).comp (continuous_apply i))

theorem archimedeanPart_archimedeanMatrix_add
    (X : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F))
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    archimedeanPart F r t (archimedeanMatrix F r t X + Y) = X + archimedeanPart F r t Y :=
  rfl

theorem archimedeanMatrix_neg_add_cancel
    (X : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F))
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    archimedeanMatrix F r t (-X) + (archimedeanMatrix F r t X + Y) = Y := by
  funext i j
  refine Prod.ext ?_ ?_
  · change -X i j + (X i j + (Y i j).1) = (Y i j).1
    abel
  · change (0 : FiniteAdeles F) + (0 + (Y i j).2) = (Y i j).2
    rw [zero_add, zero_add]

/-- **The archimedean image of the restricted open-cell Haar measure.** For an open set `R`
of adelic matrices containing `0`, stable under adding matrices with vanishing finite
components and contained in the matrices with integral finite components, there is a
constant `κ ≠ 0` such that `∫_R G(Y_∞) dY = κ ∫ G(X) dX` for every function `G` on the
archimedean matrices that is almost everywhere strongly measurable for
`archimedeanOpenCellHaar`. -/
theorem exists_setIntegral_comp_archimedeanPart
    {R : Set (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))} (hRo : IsOpen R)
    (hR0 : (0 : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) ∈ R)
    (hRadd : ∀ (X : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) (Y), Y ∈ R →
      archimedeanMatrix F r t X + Y ∈ R)
    (hRint : ∀ Y ∈ R, ∀ i j, (Y i j).2 ∈ integralFiniteAdeles F) :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ G : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F) → ℂ,
      (letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) := borel _;
        AEStronglyMeasurable G (archimedeanOpenCellHaar F r t)) →
      (letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _;
       letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) := borel _;
        ∫ Y in R, G (archimedeanPart F r t Y) ∂(openCellHaar F r t) =
          (κ : ℂ) * ∫ X, G X ∂(archimedeanOpenCellHaar F r t)) := by
  let : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
  let : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) := borel _
  have : BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := ⟨rfl⟩
  have : BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) := ⟨rfl⟩
  have : LocallyCompactSpace (Adeles F) := adeles_locallyCompactSpace F
  have : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (r + 1) → Adeles F))
  have : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (r + 1) → InfiniteAdeles F))
  have : SecondCountableTopology (InfiniteAdeles F) := infiniteAdeles_secondCountableTopology F
  have : SecondCountableTopology (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) :=
    inferInstanceAs (SecondCountableTopology (Fin (t + 1) → Fin (r + 1) → InfiniteAdeles F))
  have hμ : (openCellHaar F r t).IsAddHaarMeasure := by
    unfold openCellHaar
    infer_instance
  have hμI : (archimedeanOpenCellHaar F r t).IsAddHaarMeasure := by
    unfold archimedeanOpenCellHaar
    infer_instance
  have hπ : Measurable (archimedeanPart F r t) := continuous_archimedeanPart.measurable
  set ν := ((openCellHaar F r t).restrict R).map (archimedeanPart F r t) with hν
  have hνinv : ν.IsAddLeftInvariant := by
    refine ⟨fun X₀ => ?_⟩
    ext A hA
    have hA' : MeasurableSet ((fun X => X₀ + X) ⁻¹' A) := measurable_const_add X₀ hA
    rw [Measure.map_apply (measurable_const_add X₀) hA, hν, Measure.map_apply hπ hA,
      Measure.map_apply hπ hA', Measure.restrict_apply (hπ hA'), Measure.restrict_apply (hπ hA)]
    have e : archimedeanPart F r t ⁻¹' ((fun X => X₀ + X) ⁻¹' A) ∩ R =
        (fun Y => archimedeanMatrix F r t X₀ + Y) ⁻¹' (archimedeanPart F r t ⁻¹' A ∩ R) := by
      ext Y
      simp only [Set.mem_inter_iff, Set.mem_preimage, archimedeanPart_archimedeanMatrix_add]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, hRadd _ _ h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have h := hRadd (-X₀) _ h2
        rwa [archimedeanMatrix_neg_add_cancel] at h
    rw [e, measure_preimage_add]
  have hνfin : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [hν, Measure.map_apply hπ hKm, Measure.restrict_apply (hπ hKm)]
    let pairMap : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F) ×
        Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteAdeles F) →
        Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) := fun p i j => (p.1 i j, p.2 i j)
    have hpair : Continuous pairMap :=
      continuous_pi fun i => continuous_pi fun j =>
        ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).prodMk
          ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))
    let W : Set (Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteAdeles F)) :=
      Set.univ.pi fun _ => Set.univ.pi fun _ => (integralFiniteAdeles F : Set (FiniteAdeles F))
    have hW : IsCompact W :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles F
    have hE : IsCompact (pairMap '' (K ×ˢ W)) := (hK.prod hW).image hpair
    refine lt_of_le_of_lt (measure_mono ?_) hE.measure_lt_top
    rintro Y ⟨hY1, hY2⟩
    exact ⟨(archimedeanPart F r t Y, fun i j => (Y i j).2),
      ⟨hY1, fun i _ j _ => hRint Y hY2 i j⟩, rfl⟩
  have heq := Measure.isAddLeftInvariant_eq_smul ν (archimedeanOpenCellHaar F r t)
  set κ := Measure.addHaarScalarFactor ν (archimedeanOpenCellHaar F r t)
  have hκ : κ ≠ 0 := by
    intro h0
    have huniv : ν Set.univ = 0 := by
      rw [heq, h0, zero_smul, Measure.coe_zero, Pi.zero_apply]
    rw [hν, Measure.map_apply hπ MeasurableSet.univ, Measure.restrict_apply (hπ MeasurableSet.univ),
      Set.preimage_univ, Set.univ_inter] at huniv
    exact (hRo.measure_pos (openCellHaar F r t) ⟨0, hR0⟩).ne' huniv
  refine ⟨κ, hκ, fun G hG => ?_⟩
  have hGν : AEStronglyMeasurable G ν := by
    rw [heq]
    exact hG.smul_measure _
  change ∫ Y in R, G (archimedeanPart F r t Y) ∂(openCellHaar F r t) =
    (κ : ℂ) * ∫ X, G X ∂(archimedeanOpenCellHaar F r t)
  rw [← integral_map hπ.aemeasurable hGν, ← hν, heq, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]

end Langlands.Global.CuspidalPairEisenstein.ArchimedeanMeasure
