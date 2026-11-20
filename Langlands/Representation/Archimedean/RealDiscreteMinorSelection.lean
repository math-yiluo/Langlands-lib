import Langlands.Representation.Archimedean.RealDiscreteDonorShift
import Langlands.Representation.Archimedean.RealMinorWeightBound
import Langlands.Representation.Archimedean.RealBottomMinorTriangular

/-! # The minor columns compatible with a shifted Jacquet parameter -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealDiscreteMinorSelection

open Finset
open RealBottomMinorProducts RealBottomMinorTriangular RealDiscreteDonorShift RealMinorWeightBound

variable {n q : ℕ} {degree : Fin q → ℕ}

/-- Carry a row family to the corresponding columns of the permuted character list. -/
def permutedColumns (σ : Equiv.Perm (Fin n)) (R : Selection n degree) : Selection n degree :=
  fun t => ⟨(R t).val.map σ.symm.toEmbedding, (card_map _).trans (R t).property⟩

private theorem columnWeight_permutedColumns (σ : Equiv.Perm (Fin n))
    (R : Selection n degree) (i : Fin n) :
    columnWeight (permutedColumns σ R) i = columnWeight R (σ i) := by
  simp only [columnWeight, permutedColumns, mem_map_equiv, Equiv.symm_symm]

private theorem nested_permutedColumns (σ : Equiv.Perm (Fin n)) {R : Selection n degree}
    (hR : Nested (fun t => (R t).val)) : Nested (fun t => (permutedColumns σ R t).val) := by
  intro s t hst
  simp only [permutedColumns, card_map] at hst ⊢
  exact map_subset_map.mpr (hR s t hst)

/-- The Jacquet exponent match and the parity match force the column family to be
the row family carried to the permuted list. -/
theorem eq_permutedColumns {τ : Fin n → ℂ} {e : Fin n → Fin 2}
    {z : Fin n → ℤ} {weights : Fin n → ℕ} {r : ℝ}
    (hreal : ∀ i, (τ i).re = r + (z i : ℝ) / 2)
    (hpar : ∀ i, (e i).val = weights i % 2)
    (hmono : Monotone weights)
    (hshift : ∀ i j, z i = z j → e i = e j → weights i = weights j)
    (horder : ∀ i j, i < j → residue (z i) (e i) = residue (z j) (e j) → z j ≤ z i)
    {R C : Selection n degree} (hR : Nested (fun t => (R t).val))
    (hRweight : columnWeight R = weights) (σ p : Equiv.Perm (Fin n))
    (hexp : ∀ i, τ (σ i) - (columnWeight C i : ℂ) = τ (p i) - (weights (p i) : ℂ))
    (hCpar : ∀ i, (e (σ i)).val = columnWeight C i % 2) :
    C = permutedColumns σ R := by
  have hcard (t : Fin q) : (C t).val.card = (R t).val.card :=
    (C t).property.trans (R t).property.symm
  obtain ⟨henergy, hNested⟩ :=
    energy_le_and_nested_of_eq (fun t => (C t).val) (fun t => (R t).val) hcard hR
  have henergy' : (∑ i, columnWeight C i ^ 2) ≤ ∑ i, weights i ^ 2 := by
    change (∑ i, columnWeight C i ^ 2) ≤ ∑ i, columnWeight R i ^ 2 at henergy
    rwa [hRweight] at henergy
  have hdiff (i : Fin n) : (columnWeight C i : ℝ) =
      (weights (p i) : ℝ) + ((τ (σ i)).re - (τ (p i)).re) := by
    have h := congrArg Complex.re (hexp i)
    simp only [Complex.sub_re, Complex.natCast_re] at h
    linarith
  have hres (i : Fin n) : residue (z (σ i)) (e (σ i)) = residue (z (p i)) (e (p i)) := by
    have hd := hdiff i
    rw [hreal (σ i), hreal (p i)] at hd
    have hZ : z (σ i) - z (p i) = 2 * ((columnWeight C i : ℤ) - (weights (p i) : ℤ)) := by
      have hZ' : (z (σ i) : ℝ) - (z (p i) : ℝ) =
          2 * ((columnWeight C i : ℝ) - (weights (p i) : ℝ)) := by linarith
      exact_mod_cast hZ'
    have h₁ := hCpar i
    have h₂ := hpar (p i)
    unfold residue
    omega
  let a (i : Fin n) := (τ i).re
  let w (i : Fin n) := (weights i : ℝ)
  let m (i : Fin n) := (columnWeight C (p.symm i) : ℝ)
  let c (i : Fin n) := residue (z i) (e i)
  let π := p.symm.trans σ
  have hπ (i : Fin n) : c (π i) = c i := by
    simpa only [c, π, Equiv.trans_apply, Equiv.apply_symm_apply] using hres (p.symm i)
  have hanti (i j : Fin n) (hc : c i = c j) (ha : a i < a j) : w j ≤ w i := by
    rcases le_or_gt j i with hj | hj
    · dsimp only [w]
      exact_mod_cast hmono hj
    · have hz : (z j : ℝ) ≤ (z i : ℝ) := by exact_mod_cast horder i j hj hc
      dsimp only [a] at ha
      rw [hreal i, hreal j] at ha
      linarith
  have hm (i : Fin n) : m i = w i + (a (π i) - a i) := by
    simpa only [m, w, a, π, Equiv.trans_apply, Equiv.apply_symm_apply] using hdiff (p.symm i)
  have hbound : (∑ i, m i ^ 2) ≤ ∑ i, w i ^ 2 := by
    have hs : (∑ i, m i ^ 2) = ∑ i, (columnWeight C i : ℝ) ^ 2 :=
      p.symm.sum_comp (fun i => (columnWeight C i : ℝ) ^ 2)
    rw [hs]
    dsimp only [w]
    exact_mod_cast henergy'
  have hzero := eq_of_energy_le_of_antivary c a w m π hπ hanti hm hbound
  have hCweight (i : Fin n) : columnWeight C i = weights (σ i) := by
    have hi := hzero (p i)
    simp only [a, m, w, π, Equiv.trans_apply, Equiv.symm_apply_apply] at hi
    have hz : z (σ i) = z (p i) := by
      have hre := hi.1
      rw [hreal (σ i), hreal (p i)] at hre
      have h' : (z (σ i) : ℝ) = (z (p i) : ℝ) := by linarith
      exact_mod_cast h'
    have he : e (σ i) = e (p i) := by
      have h := hres i
      rw [hz] at h
      have h₁ := (e (σ i)).isLt
      have h₂ := (e (p i)).isLt
      apply Fin.ext
      unfold residue at h
      omega
    have wh := hshift (σ i) (p i) hz he
    have hw : columnWeight C i = weights (p i) := by exact_mod_cast hi.2
    exact hw.trans wh.symm
  have hNC : Nested (fun t => (C t).val) := by
    apply hNested
    change (∑ i, columnWeight C i ^ 2) = ∑ i, columnWeight R i ^ 2
    simp_rw [hCweight, hRweight]
    exact Equiv.sum_comp σ (fun i => weights i ^ 2)
  have hsets := eq_of_nested_of_weight_eq hNC (nested_permutedColumns σ hR)
    (fun t => (C t).property.trans (permutedColumns σ R t).property.symm) (fun i => by
      change columnWeight C i = columnWeight (permutedColumns σ R) i
      rw [hCweight, columnWeight_permutedColumns, hRweight])
  funext t
  exact Subtype.ext (congrFun hsets t)

end Langlands.Archimedean.RealDiscreteMinorSelection
