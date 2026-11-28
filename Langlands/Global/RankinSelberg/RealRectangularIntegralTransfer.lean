import Langlands.Representation.RankinSelberg.Measures
import Langlands.HarmonicAnalysis.RowFourier
import Mathlib.MeasureTheory.Integral.Prod

/-! # Finite integral comparison along rectangular prefixes -/

noncomputable section

open MeasureTheory Matrix Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealRectangularRows

open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.RankinSelberg (rectangularMeasure)

local notation "Row" => fun t : ℕ => Fin (t + 1) → ℝ
local notation "X" => fun j t : ℕ => Matrix (Fin j) (Fin (t + 1)) ℝ

variable {Q V : Type*} [MeasurableSpace Q] (t : ℕ) (μ : Measure Q) [SFinite μ]
  (ν : AdditiveHaarMeasure ℝ) [SigmaFinite ν.measure]

private def appendEquiv (j : ℕ) : (Q × X j t) × Row t ≃ᵐ Q × X (j + 1) t :=
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => Row t) (Fin.last j)).trans
    MeasurableEquiv.prodComm
  MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl Q).prodCongr e.symm)

private theorem appendEquiv_apply (j : ℕ) (p : (Q × X j t) × Row t) :
    appendEquiv (Q := Q) t j p = (p.1.1, Fin.lastCases p.2 p.1.2) := by
  refine Prod.ext rfl ?_
  change @Fin.insertNth j (fun _ => Row t) (Fin.last j) p.2 p.1.2 = Fin.lastCases p.2 p.1.2
  rw [Fin.insertNth_last']
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp
  · simp

private theorem measurePreserving_appendEquiv (j : ℕ) : MeasurePreserving (appendEquiv (Q := Q) t j)
    ((μ.prod (rectangularMeasure ν j (t + 1))).prod (rowMeasure ν (t + 1)))
    (μ.prod (rectangularMeasure ν (j + 1) (t + 1))) := by
  let m := rowMeasure ν (t + 1)
  let M := rectangularMeasure ν j (t + 1)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => Row t) (Fin.last j)).trans
    MeasurableEquiv.prodComm
  have hsplit : MeasurePreserving e (rectangularMeasure ν (j + 1) (t + 1)) (M.prod m) :=
    (Measure.measurePreserving_swap (μ := m) (ν := M)).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (j + 1) => m) (Fin.last j))
  exact ((MeasurePreserving.id μ).prod (hsplit.symm e)).comp (measurePreserving_prodAssoc μ M m)

private theorem integrable_iff_append (j : ℕ) (F : Q × X (j + 1) t → ℂ)
    (hF : Integrable F (μ.prod (rectangularMeasure ν (j + 1) (t + 1)))) :
    Integrable (fun p : (Q × X j t) × Row t => F (p.1.1, Fin.lastCases p.2 p.1.2))
      ((μ.prod (rectangularMeasure ν j (t + 1))).prod (rowMeasure ν (t + 1))) := by
  have he := (measurePreserving_appendEquiv (Q := Q) t μ ν j).integrable_comp_of_integrable hF
  change Integrable (fun p => F (appendEquiv (Q := Q) t j p)) _ at he
  simpa only [appendEquiv_apply] using he

private theorem integral_eq_append (j : ℕ) (F : Q × X (j + 1) t → ℂ)
    (hF : Integrable F (μ.prod (rectangularMeasure ν (j + 1) (t + 1)))) :
    (∫ p, F p ∂(μ.prod (rectangularMeasure ν (j + 1) (t + 1)))) =
      ∫ p : Q × X j t, (∫ y, F (p.1, Fin.lastCases y p.2) ∂(rowMeasure ν (t + 1)))
        ∂(μ.prod (rectangularMeasure ν j (t + 1))) := by
  have hp := (measurePreserving_appendEquiv (Q := Q) t μ ν j).integral_comp
    (appendEquiv (Q := Q) t j).measurableEmbedding F
  simp only [appendEquiv_apply] at hp
  rw [← hp, integral_prod _ (integrable_iff_append t μ ν j F hF)]

/-- A finite prefix-to-next-prefix kernel comparison extends to a finite integral comparison
with any terminal rectangle. Absolute convergence descends from the terminal kernels. -/
def RealRectangularIntegralTransferStatement : Prop :=
  ∀ (k : ℕ) (K : ∀ j : ℕ, V → ℂ → Q × X j t → ℂ),
    (∀ j < k, ∀ v : V, ∃ (n : ℕ) (w : Fin n → V), ∀ (s : ℂ) (p : Q × X j t),
      K j v s p = ∑ i, ∫ y, K (j + 1) (w i) s (p.1, Fin.lastCases y p.2) ∂(rowMeasure ν (t + 1))) →
    ∀ j ≤ k, ∀ v : V, ∃ (n : ℕ) (w : Fin n → V), ∀ s : ℂ,
      (∀ i, Integrable (K k (w i) s) (μ.prod (rectangularMeasure ν k (t + 1)))) →
      Integrable (K j v s) (μ.prod (rectangularMeasure ν j (t + 1))) ∧
      (∫ p, K j v s p ∂(μ.prod (rectangularMeasure ν j (t + 1)))) =
        ∑ i, ∫ p, K k (w i) s p ∂(μ.prod (rectangularMeasure ν k (t + 1)))

set_option maxHeartbeats 750000 in
theorem realRectangularIntegralTransfer : RealRectangularIntegralTransferStatement (V := V) t μ ν := by
  intro k K H j hj
  let m (j : ℕ) := μ.prod (rectangularMeasure ν j (t + 1))
  let Goal (j : ℕ) := ∀ v : V, ∃ (n : ℕ) (w : Fin n → V), ∀ s : ℂ,
    (∀ i, Integrable (K k (w i) s) (m k)) → Integrable (K j v s) (m j) ∧
    (∫ p, K j v s p ∂(m j)) = ∑ i, ∫ p, K k (w i) s p ∂(m k)
  refine Nat.decreasingInduction (motive := fun j _ => Goal j) ?_ ?_ hj
  · intro j hj ih v
    obtain ⟨l, u, hu⟩ := H j (Nat.lt_of_succ_le hj) v
    choose n w hw using fun i => ih (u i)
    let J := Σ i : Fin l, Fin (n i)
    let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
    refine ⟨Fintype.card J, fun i => w (e i).1 (e i).2, fun s hs => ?_⟩
    have hTerm (i : Fin l) (d : Fin (n i)) : Integrable (K k (w i d) s) (m k) := by
      let p : J := ⟨i, d⟩
      have hOne := hs (e.symm p)
      change Integrable (K k (w (e (e.symm p)).1 (e (e.symm p)).2) s) (m k) at hOne
      rw [e.apply_symm_apply] at hOne
      exact hOne
    have hNext (i : Fin l) := hw i s (hTerm i)
    let F (i : Fin l) (p : Q × X j t) := ∫ y, K (j + 1) (u i) s
      (p.1, Fin.lastCases y p.2) ∂(rowMeasure ν (t + 1))
    have hF (i : Fin l) : Integrable (F i) (m j) :=
      (integrable_iff_append t μ ν j _ (hNext i).1).integral_prod_left
    have hK : K j v s = fun p => ∑ i, F i p := funext (hu s)
    refine ⟨by rw [hK]; exact integrable_finsetSum _ fun i _ => hF i, ?_⟩
    calc
      _ = ∑ i, ∫ p, F i p ∂(m j) := by rw [hK, integral_finsetSum _ fun i _ => hF i]
      _ = ∑ i, ∫ p, K (j + 1) (u i) s p ∂(m (j + 1)) := by
        exact Finset.sum_congr rfl fun i _ => (integral_eq_append t μ ν j _ (hNext i).1).symm
      _ = ∑ i, ∑ d, ∫ p, K k (w i d) s p ∂(m k) :=
        Finset.sum_congr rfl fun i _ => (hNext i).2
      _ = ∑ p : J, ∫ q, K k (w p.1 p.2) s q ∂(m k) :=
        (Fintype.sum_sigma (fun p : J => ∫ q, K k (w p.1 p.2) s q ∂(m k))).symm
      _ = _ := (Equiv.sum_comp e _).symm
  · intro v
    exact ⟨1, fun _ => v, fun s hs => ⟨hs 0, by simp⟩⟩

end Langlands.Global.RankinSelbergGlobal.RealRectangularRows
