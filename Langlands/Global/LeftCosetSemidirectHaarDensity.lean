import Langlands.Global.LeftCosetSemidirectFiniteVolume
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Haar density for multiplication in radical-first order -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace.Semidirect

universe u v w

variable {N : Type u} {M : Type v} {H : Type w}
  [Group N] [Group M] [Group H] [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace H]
  [IsTopologicalGroup N] [IsTopologicalGroup M] [IsTopologicalGroup H]
  (i : N →* H) (j : M →* H) (p : H →* M)
  (hpj : ∀ m, p (j m) = m) (hker : ∀ h, p h = 1 → ∃ n, i n = h)
  (hpi : ∀ n, p (i n) = 1) (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p)

/-- Multiplication in complement-first order. It is obtained from radical-first order by
inverting the inputs, swapping them, and inverting the output. -/
def complementFirstHomeomorph : M × N ≃ₜ H :=
  (Homeomorph.prodComm M N).trans
    (((Homeomorph.inv N).prodCongr (Homeomorph.inv M)).trans
      ((prodHomeomorph i j p hpj hker hpi hi hj hp).trans (Homeomorph.inv H)))

@[simp] theorem complementFirstHomeomorph_apply (q : M × N) :
    complementFirstHomeomorph i j p hpj hker hpi hi hj hp q = j q.1 * i q.2 := by
  change (i q.2⁻¹ * j q.1⁻¹)⁻¹ = _
  simp

private theorem project_complementFirstHomeomorph (q : M × N) :
    p (complementFirstHomeomorph i j p hpj hker hpi hi hj hp q) = q.1 := by
  rw [complementFirstHomeomorph_apply, map_mul, hpj, hpi, mul_one]

variable [MeasurableSpace N] [MeasurableSpace M] [MeasurableSpace H]
  [BorelSpace N] [BorelSpace M] [BorelSpace H]
  [SecondCountableTopology N]

/-- Haar in complement-first coordinates is the unweighted product. Left multiplication
acts by a fixed left translation of the complement and by left translation in each
normal fiber. -/
theorem isHaarMeasure_map_complementFirst (dn : Measure N) (dm : Measure M)
    [dn.IsHaarMeasure] [dm.IsHaarMeasure] [SFinite dn] [SFinite dm] :
    (Measure.map (complementFirstHomeomorph i j p hpj hker hpi hi hj hp)
      (dm.prod dn)).IsHaarMeasure := by
  let E := complementFirstHomeomorph i j p hpj hker hpi hi hj hp
  have hE : Measurable E := E.continuous.measurable
  let : IsFiniteMeasureOnCompacts (Measure.map E (dm.prod dn)) :=
    IsFiniteMeasureOnCompacts.map _ E
  let : IsOpenPosMeasure (Measure.map E (dm.prod dn)) :=
    E.continuous.isOpenPosMeasure_map E.surjective
  change (Measure.map E (dm.prod dn)).IsHaarMeasure
  refine { map_mul_left_eq_self := fun g => ?_ }
  let k := fun m : M => (E.symm (g * j m)).2
  have hk : Continuous k :=
    (E.symm.continuous.comp (continuous_const.mul hj)).snd
  have hfirst (m : M) : (E.symm (g * j m)).1 = p g * m := calc
    _ = p (E (E.symm (g * j m))) :=
      (project_complementFirstHomeomorph i j p hpj hker hpi hi hj hp _).symm
    _ = p g * m := by rw [E.apply_symm_apply, map_mul, hpj]
  let L := fun q : M × N => (p g * q.1, k q.1 * q.2)
  have hL : MeasurePreserving L (dm.prod dn) (dm.prod dn) :=
    (measurePreserving_mul_left dm (p g)).skew_product
      ((hk.comp continuous_fst).mul continuous_snd).measurable
      (Filter.Eventually.of_forall fun m => (measurePreserving_mul_left dn (k m)).map_eq)
  have hcomm : (g * ·) ∘ E = E ∘ L := by
    funext q
    change g * E q = E (p g * q.1, k q.1 * q.2)
    have hgj : g * j q.1 = j (p g * q.1) * i (k q.1) := by
      calc
        _ = E (E.symm (g * j q.1)) := (E.apply_symm_apply _).symm
        _ = _ := by
          rw [show E = complementFirstHomeomorph i j p hpj hker hpi hi hj hp from rfl,
            complementFirstHomeomorph_apply]
          change j (E.symm (g * j q.1)).1 * i (k q.1) = _
          rw [hfirst]
    simp only [E, complementFirstHomeomorph_apply, map_mul, ← mul_assoc, hgj]
  rw [Measure.map_map (measurable_const_mul _) hE, hcomm, ← Measure.map_map hE hL.measurable,
    hL.map_eq]

variable [LocallyCompactSpace N]

/-- The inverse modulus of conjugation by the complement, as a measure density. -/
def inverseConjugationModulus (m : M) : ℝ≥0∞ :=
  ((mulEquivHaarChar (conj i j p hpj hker hpi hi hj m))⁻¹ : ℝ≥0)

omit [IsTopologicalGroup M] [MeasurableSpace H] [BorelSpace H] in
theorem measurable_inverseConjugationModulus :
    Measurable (inverseConjugationModulus i j p hpj hker hpi hi hj) := by
  exact measurable_coe_nnreal_ennreal.comp
    (measurable_mulEquivHaarChar_conj hpj hker hpi hi hj).inv

/-- Switching to radical-first coordinates introduces the inverse conjugation modulus in
the complement factor. -/
theorem map_complementFirst_eq_map_weightedProduct (dn : Measure N) (dm : Measure M)
    [dn.IsHaarMeasure] [SFinite dn] [SFinite dm] :
    Measure.map (complementFirstHomeomorph i j p hpj hker hpi hi hj hp) (dm.prod dn) =
      Measure.map (prodHomeomorph i j p hpj hker hpi hi hj hp)
        (dn.prod (dm.withDensity (inverseConjugationModulus i j p hpj hker hpi hi hj))) := by
  let E := complementFirstHomeomorph i j p hpj hker hpi hi hj hp
  let B := prodHomeomorph i j p hpj hker hpi hi hj hp
  let α := conj i j p hpj hker hpi hi hj
  let d := inverseConjugationModulus i j p hpj hker hpi hi hj
  let : dn.Regular := inferInstance
  have hd : Measurable d := measurable_inverseConjugationModulus i j p hpj hker hpi hi hj
  have hα (m : M) : dn.map (α m) = (mulEquivHaarChar (α m))⁻¹ • dn := by
    calc
      _ = (mulEquivHaarChar (α m))⁻¹ • (mulEquivHaarChar (α m) • dn.map (α m)) := by
        rw [smul_smul, inv_mul_cancel₀ (mulEquivHaarChar_pos (α m)).ne', one_smul]
      _ = _ := by rw [mulEquivHaarChar_smul_map]
  have hconvert (m : M) (n : N) : E (m, n) = B (α m n, m) := by
    change complementFirstHomeomorph i j p hpj hker hpi hi hj hp (m, n) = _
    rw [complementFirstHomeomorph_apply, prodHomeomorph_apply, i_conj]
    group
  ext s hs
  have hBs : MeasurableSet (B ⁻¹' s) := B.continuous.measurable hs
  have hφ : Measurable (fun m => dn ((fun n => (n, m)) ⁻¹' (B ⁻¹' s))) :=
    measurable_measure_prodMk_left (measurable_swap hBs)
  change Measure.map E (dm.prod dn) s = Measure.map B (dn.prod (dm.withDensity d)) s
  rw [Measure.map_apply E.continuous.measurable hs, Measure.map_apply B.continuous.measurable hs,
    Measure.prod_apply (E.continuous.measurable hs), Measure.prod_apply_symm hBs,
    lintegral_withDensity_eq_lintegral_mul _ hd hφ]
  apply lintegral_congr
  intro m
  let S := (fun n : N => (n, m)) ⁻¹' (B ⁻¹' s)
  have hS : MeasurableSet S := (measurable_id.prodMk measurable_const) hBs
  have hpre : Prod.mk m ⁻¹' (E ⁻¹' s) = α m ⁻¹' S := by
    ext n
    exact show E (m, n) ∈ s ↔ B (α m n, m) ∈ s by rw [hconvert]
  have hmeas : Measurable (fun n => α m n) := (α m).toHomeomorph.continuous.measurable
  rw [hpre, ← Measure.map_apply hmeas hS, show (fun n => α m n) = α m from rfl, hα,
    Measure.smul_apply]
  rfl

/-- Left Haar in radical-first coordinates, with the inverse modular density on the
complement. -/
theorem isHaarMeasure_map_weightedProduct (dn : Measure N) (dm : Measure M)
    [dn.IsHaarMeasure] [dm.IsHaarMeasure] [SFinite dn] [SFinite dm] :
    (Measure.map (prodHomeomorph i j p hpj hker hpi hi hj hp)
      (dn.prod (dm.withDensity (inverseConjugationModulus i j p hpj hker hpi hi hj)))).IsHaarMeasure := by
  rw [← map_complementFirst_eq_map_weightedProduct i j p hpj hker hpi hi hj hp dn dm]
  exact isHaarMeasure_map_complementFirst i j p hpj hker hpi hi hj hp dn dm

end Langlands.Global.LeftCosetSpace.Semidirect
