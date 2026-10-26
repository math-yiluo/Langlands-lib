import Langlands.Representation.RankinSelberg.CompactIntegrationStatement
import Langlands.Representation.RankinSelberg.CompactDataProof
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Finite measurable partitions compute compact averages uniformly. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

namespace CompactIntegration

theorem finite_average {A B : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A] (D : A → B)
    (hD : IsLocallyConstant D) (hfin : (Set.range D).Finite)
    (μ : Measure A) [IsFiniteMeasure μ] :
    ∃ (m : ℕ) (k : Fin m → A) (c : Fin m → ℝ),
      (∀ i, 0 ≤ c i) ∧ (∑ i, c i) = μ.real Set.univ ∧
      ∀ H : A → ℂ, (∀ x y, D x = D y → H x = H y) →
        Integrable H μ ∧
        (∫ x, H x ∂μ) = ∑ i, (c i : ℂ) * H (k i) ∧
        (∫⁻ x, ‖H x‖ₑ ∂μ) = ∑ i, ENNReal.ofReal (c i) * ‖H (k i)‖ₑ := by
  classical
  let I := Set.range D
  let : Fintype I := hfin.fintype
  let m := Fintype.card I
  let e : I ≃ Fin m := Fintype.equivFin I
  let label : A → Fin m := fun x => e ⟨D x, x, rfl⟩
  have hlabel_eq (x y : A) : label x = label y ↔ D x = D y := by
    simp only [label, e.injective.eq_iff]
    exact Subtype.ext_iff
  have hlabel : Measurable label := by
    apply measurable_to_countable
    intro y
    have heq : label ⁻¹' {label y} = {x | D x = D y} := by
      ext x
      exact hlabel_eq x y
    rw [heq]
    exact (hD.isOpen_fiber (D y)).measurableSet
  let k : Fin m → A := fun i => Classical.choose (e.symm i).property
  have hk (i : Fin m) : D (k i) = (e.symm i).val :=
    Classical.choose_spec (e.symm i).property
  have hfactor (x : A) : D (k (label x)) = D x := by
    rw [hk]
    simp [label]
  let ν := Measure.map label μ
  let c : Fin m → ℝ := fun i => ν.real {i}
  refine ⟨m, k, c, fun i => measureReal_nonneg, ?_, ?_⟩
  · calc
      ∑ i, c i = ν.real Set.univ := by
        simp [c, sum_measureReal_singleton]
      _ = μ.real Set.univ := by
        simp [ν, map_measureReal_apply hlabel MeasurableSet.univ]
  · intro H hH
    let h : Fin m → ℂ := fun i => H (k i)
    have hcomp : (fun x => h (label x)) = H := by
      funext x
      exact hH _ _ (hfactor x)
    have hi : Integrable h ν :=
      (SimpleFunc.ofFinite h).integrable_of_isFiniteMeasure
    have hm : StronglyMeasurable h :=
      (measurable_of_finite h).stronglyMeasurable
    have hHi : Integrable H μ := by
      rw [← hcomp]
      exact (integrable_map_measure hm.aestronglyMeasurable hlabel.aemeasurable).mp hi
    refine ⟨hHi, ?_, ?_⟩
    · calc
        ∫ x, H x ∂μ = ∫ i, h i ∂ν := by
          rw [integral_map_of_stronglyMeasurable hlabel hm, hcomp]
        _ = ∑ i, (c i : ℂ) * H (k i) := by
          simpa [c, h, Complex.real_smul] using (integral_fintype hi)
    · calc
        ∫⁻ x, ‖H x‖ₑ ∂μ = ∫⁻ i, ‖h i‖ₑ ∂ν := by
          rw [lintegral_map (measurable_of_finite _) hlabel]
          exact lintegral_congr (fun x => congrArg (fun z : ℂ => ‖z‖ₑ) (congrFun hcomp x).symm)
        _ = ∑ i, ENNReal.ofReal (c i) * ‖H (k i)‖ₑ := by
          rw [lintegral_fintype]
          apply Finset.sum_congr rfl
          intro i _
          simp only [c, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top ν {i})]
          exact mul_comm _ _

end CompactIntegration

universe uF uV uW

/-- A single finite measurable partition computes all compact averages of the
specified equal-rank data, including the extended absolute integrals. -/
theorem equalRankCompactIntegration (F : Type uF) [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] (n : ℕ) :
    EqualRankCompactIntegrationStatement.{uF, uV, uW} F n := by
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  intro K hK κ _ abv hdet V _ _ W _ _ π σ hπ hσ ψ ℓ ℓ' f f' Φ
  let D := fun z : Langlands.GeneralLinear (n + 1) F =>
    (modelRepresentation π ℓ z f, modelRepresentation σ ℓ' z f',
      fun x : Fin (n + 1) → F => Φ (Matrix.vecMul x z.val))
  have hdata := equalRankCompactData F n V W π σ hπ hσ ψ ℓ ℓ' f f' Φ
  obtain ⟨m, k, c, hc, hmass, havg⟩ :=
    CompactIntegration.finite_average (fun z : K => D z.val)
      (hdata.1.comp_continuous continuous_subtype_val) (hdata.2 K hK) κ
  refine ⟨m, k, c, hc, hmass, ?_⟩
  intro g s
  apply havg
  intro x y hxy
  have hf : f.val.val (g * x.val) = f.val.val (g * y.val) :=
    congrArg (fun z => z.val.val g) (congrArg Prod.fst hxy)
  have hf' : f'.val.val (g * x.val) = f'.val.val (g * y.val) :=
    congrArg (fun z => z.val.val g) (congrArg (fun z => z.2.1) hxy)
  have hrow : Φ (lastRow (g * x.val)) = Φ (lastRow (g * y.val)) := by
    exact congrFun (congrArg (fun z => z.2.2) hxy) (lastRow g)
  have hweight (z : K) :
      determinantWeight abv (g * z.val) s = determinantWeight abv g s := by
    simp [determinantWeight, Matrix.det_mul, map_mul, hdet z]
  simp only [equalRankFunction, hf, hf', hrow, hweight]

end Langlands.RankinSelberg
