import Langlands.Representation.RankinSelberg.Measures
import Langlands.HarmonicAnalysis.RowFourier
import Mathlib.MeasureTheory.Integral.Prod

/-! Product-measure row splitting for the first-block Laurent calculation. -/

noncomputable section

open MeasureTheory
open Langlands.HarmonicAnalysis

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

universe uK uA uB

/-- Separate the last row, with that row first in the resulting product. -/
def rowSplitEquiv (K : Type uK) [MeasurableSpace K] (m a : ℕ) :
    Matrix (Fin (m + 1)) (Fin a) K ≃ᵐ
      (Fin a → K) × Matrix (Fin m) (Fin a) K :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin a → K) (Fin.last m)

@[simp] theorem rowSplitEquiv_symm_apply {K : Type uK} [MeasurableSpace K]
    (m a : ℕ) (p : (Fin a → K) × Matrix (Fin m) (Fin a) K) :
    (rowSplitEquiv K m a).symm p =
      (fun i => Fin.snoc (α := fun _ => Fin a → K) (fun j => p.2 j) p.1 i :
        Matrix (Fin (m + 1)) (Fin a) K) := by
  change Fin.insertNth (α := fun _ => Fin a → K) (Fin.last m) p.1 p.2 = _
  exact Fin.insertNth_last' p.1 p.2

section Rectangular

variable {K : Type uK} [AddGroup K] [TopologicalSpace K] [MeasurableSpace K]
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure]

theorem measurePreserving_rowSplitEquiv (m a : ℕ) :
    MeasurePreserving (rowSplitEquiv K m a)
      (rectangularMeasure ν (m + 1) a)
      ((rowMeasure ν a).prod (rectangularMeasure ν m a)) := by
  exact measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => rowMeasure ν a) (Fin.last m)

/-- Appending the row to the remaining rectangle preserves the supplied product measure. -/
theorem measurePreserving_rowSnoc (m a : ℕ) :
    MeasurePreserving
      (fun p : (Fin a → K) × Matrix (Fin m) (Fin a) K =>
        (fun i => Fin.snoc (α := fun _ => Fin a → K) (fun j => p.2 j) p.1 i :
          Matrix (Fin (m + 1)) (Fin a) K))
      ((rowMeasure ν a).prod (rectangularMeasure ν m a))
      (rectangularMeasure ν (m + 1) a) := by
  have he : (⇑(rowSplitEquiv K m a).symm) =
      (fun p : (Fin a → K) × Matrix (Fin m) (Fin a) K =>
        (fun i => Fin.snoc (α := fun _ => Fin a → K) (fun j => p.2 j) p.1 i :
          Matrix (Fin (m + 1)) (Fin a) K)) :=
    funext (rowSplitEquiv_symm_apply m a)
  rw [← he]
  exact (measurePreserving_rowSplitEquiv ν m a).symm

/-- Absolute integrability justifies both the row split and the inner Fubini swap. -/
theorem integral_rectangular_rowSnoc {α : Type uA} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (m a : ℕ)
    (H : Matrix (Fin (m + 1)) (Fin a) K → α → ℂ)
    (hH : AEStronglyMeasurable (Function.uncurry H)
      ((rectangularMeasure ν (m + 1) a).prod μ))
    (hfin : (∫⁻ Z, ∫⁻ q, ‖H Z q‖ₑ ∂μ ∂rectangularMeasure ν (m + 1) a) ≠ ⊤) :
    Integrable (fun x => ∫ q, ∫ y,
      H (fun i => Fin.snoc (α := fun _ => Fin a → K) (fun j => y j) x i) q
      ∂rectangularMeasure ν m a ∂μ) (rowMeasure ν a) ∧
    (∫ Z, ∫ q, H Z q ∂μ ∂rectangularMeasure ν (m + 1) a) =
      ∫ x, ∫ q, ∫ y,
        H (fun i => Fin.snoc (α := fun _ => Fin a → K) (fun j => y j) x i) q
        ∂rectangularMeasure ν m a ∂μ ∂rowMeasure ν a := by
  let e := (rowSplitEquiv K m a).symm
  have he : MeasurePreserving e
      ((rowMeasure ν a).prod (rectangularMeasure ν m a))
      (rectangularMeasure ν (m + 1) a) :=
    (measurePreserving_rowSplitEquiv ν m a).symm
  have hi : Integrable (Function.uncurry H)
      ((rectangularMeasure ν (m + 1) a).prod μ) := by
    refine ⟨hH, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hH.enorm]
    exact lt_top_iff_ne_top.mpr hfin
  have hs := (he.prod (MeasurePreserving.id μ)).integrable_comp_of_integrable hi
  have ht := (measurePreserving_prodAssoc (rowMeasure ν a)
    (rectangularMeasure ν m a) μ).symm.integrable_comp_of_integrable hs
  have hx : ∀ᵐ x ∂rowMeasure ν a,
      Integrable (fun p : Matrix (Fin m) (Fin a) K × α => H (e (x, p.1)) p.2)
        ((rectangularMeasure ν m a).prod μ) :=
    ht.prod_right_ae
  have hswap : (fun x => ∫ y, ∫ q, H (e (x, y)) q ∂μ
      ∂rectangularMeasure ν m a) =ᵐ[rowMeasure ν a]
      (fun x => ∫ q, ∫ y, H (e (x, y)) q ∂rectangularMeasure ν m a ∂μ) := by
    filter_upwards [hx] with x hxi
    exact integral_integral_swap hxi
  have hj := he.integrable_comp_of_integrable hi.integral_prod_left
  have hout := hj.integral_prod_left.congr hswap
  constructor
  · simpa only [e, rowSplitEquiv_symm_apply] using hout
  · calc
      (∫ Z, ∫ q, H Z q ∂μ ∂rectangularMeasure ν (m + 1) a) =
          ∫ p, ∫ q, H (e p) q ∂μ
            ∂(rowMeasure ν a).prod (rectangularMeasure ν m a) :=
        (he.integral_comp' (fun Z => ∫ q, H Z q ∂μ)).symm
      _ = ∫ x, ∫ y, ∫ q, H (e (x, y)) q ∂μ
          ∂rectangularMeasure ν m a ∂rowMeasure ν a := integral_prod _ hj
      _ = ∫ x, ∫ q, ∫ y, H (e (x, y)) q
          ∂rectangularMeasure ν m a ∂μ ∂rowMeasure ν a := integral_congr_ae hswap
      _ = _ := by simp only [e, rowSplitEquiv_symm_apply]

/-- Every entry uses the original scalar measure, including in zero dimensions. -/
theorem rectangularMeasure_entries_pow (j t : ℕ) (S : Set K) :
    rectangularMeasure ν j t {x | ∀ a b, x a b ∈ S} = ν.measure S ^ (j * t) := by
  have he : {x : Matrix (Fin j) (Fin t) K | ∀ a b, x a b ∈ S} =
      Set.univ.pi (fun _ : Fin j => Set.univ.pi (fun _ : Fin t => S)) := by
    ext x
    change (∀ a b, x a b ∈ S) ↔
      (∀ a ∈ Set.univ, ∀ b ∈ Set.univ, x a b ∈ S)
    simp
  rw [he]
  change (Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin t => ν.measure)) :
    Measure (Fin j → Fin t → K))
      (Set.univ.pi (fun _ : Fin j => Set.univ.pi (fun _ : Fin t => S))) = _
  simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Nat.mul_comm t j]

/-- Transposing the rectangular dimensions leaves an entry-cube's mass unchanged. -/
theorem rectangularMeasure_entries_swap (a b : ℕ) (S : Set K) :
    rectangularMeasure ν a b {x | ∀ i j, x i j ∈ S} =
      rectangularMeasure ν b a {x | ∀ i j, x i j ∈ S} := by
  rw [rectangularMeasure_entries_pow, rectangularMeasure_entries_pow, Nat.mul_comm]

end Rectangular

section IntegerCube

variable {K : Type uK} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [MeasurableSpace K]
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure]

/-- The valuation-integer cube has the product mass of its actual entries. -/
theorem rectangularMeasure_integer_cube (j t : ℕ) :
    rectangularMeasure ν j t
        {x | ∀ a b, x a b ∈ (ValuativeRel.valuation K).integer} =
      ν.measure ((ValuativeRel.valuation K).integer : Set K) ^ (j * t) :=
  rectangularMeasure_entries_pow ν j t _

/-- The two integral cubes occurring in the first-block comparison have equal mass. -/
theorem rectangularMeasure_integer_cube_swap (a b : ℕ) :
    rectangularMeasure ν a b
        {x | ∀ i j, x i j ∈ (ValuativeRel.valuation K).integer} =
      rectangularMeasure ν b a
        {x | ∀ i j, x i j ∈ (ValuativeRel.valuation K).integer} :=
  rectangularMeasure_entries_swap ν a b _

end IntegerCube

/-- A bounded jointly measurable kernel allows an integrable product to be rearranged. -/
theorem integral_mul_integral_swap {α : Type uA} {β : Type uB}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ρ : Measure β)
    [SFinite μ] [SFinite ρ] (A : α → ℂ) (Φ : β → ℂ) (Kf : β → α → ℂ)
    (hA : Integrable A μ) (hΦ : Integrable Φ ρ)
    (hK : AEStronglyMeasurable (Function.uncurry Kf) (ρ.prod μ))
    (hKle : ∀ x q, ‖Kf x q‖ ≤ 1) :
    Integrable (fun x => Φ x * ∫ q, Kf x q * A q ∂μ) ρ ∧
    (∫ x, Φ x * ∫ q, Kf x q * A q ∂μ ∂ρ) =
      ∫ q, A q * ∫ x, Kf x q * Φ x ∂ρ ∂μ := by
  have hm : AEStronglyMeasurable
      (fun p : β × α => Φ p.1 * (Kf p.1 p.2 * A p.2)) (ρ.prod μ) :=
    hΦ.aestronglyMeasurable.comp_fst.mul (hK.mul hA.aestronglyMeasurable.comp_snd)
  have hi : Integrable
      (fun p : β × α => Φ p.1 * (Kf p.1 p.2 * A p.2)) (ρ.prod μ) := by
    refine (hΦ.mul_prod hA).mono hm ?_
    filter_upwards with p
    simp only [norm_mul]
    calc
      ‖Φ p.1‖ * (‖Kf p.1 p.2‖ * ‖A p.2‖) ≤ ‖Φ p.1‖ * (1 * ‖A p.2‖) := by
        gcongr
        exact hKle p.1 p.2
      _ = ‖Φ p.1‖ * ‖A p.2‖ := by rw [one_mul]
  constructor
  · simpa only [integral_const_mul] using hi.integral_prod_left
  · calc
      (∫ x, Φ x * ∫ q, Kf x q * A q ∂μ ∂ρ) =
          ∫ x, ∫ q, Φ x * (Kf x q * A q) ∂μ ∂ρ := by
        simp only [integral_const_mul]
      _ = ∫ q, ∫ x, Φ x * (Kf x q * A q) ∂ρ ∂μ := integral_integral_swap hi
      _ = ∫ q, A q * ∫ x, Kf x q * Φ x ∂ρ ∂μ := by
        apply integral_congr_ae
        filter_upwards with q
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        ring

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
