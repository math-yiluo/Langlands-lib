import Langlands.LinearAlgebra.TypeD4CyclicPairRoots
import Langlands.LinearAlgebra.RootDatumCoweightFace

/-! # A simple base adapted to the cyclic A2 face in type D4 -/

noncomputable section

open Matrix IsAddIndecomposable
open Langlands.GroupScheme.SplitExistence

namespace Langlands.LinearAlgebra

variable {I X Y : Type*} [Finite I] [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum I X Y) [P.IsReduced] (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
  (e : b.support ≃ Fin 4)
  (hD : ∀ a c : b.support, P.pairing a.val c.val = CartanMatrix.D 4 (e a) (e c))

include hspan hD in
/-- Each D4 A2 pair admits a cocharacter and a compatible base with precisely
the two given simple zero roots. -/
theorem exists_d4A2_basedZeroFace (i j : I) (hij : P.pairing i j = -1) :
    ∃ (ν : Y) (B : P.Base),
      (∀ k, P.root' k ν = 0 ↔ k ∈ d4A2CorootSet P i j) ∧
      (∀ k ∈ B.support, 0 ≤ P.root' k ν) ∧
      ∀ k : I, k ∈ B.support ∧ P.root' k ν = 0 ↔ k = i ∨ k = j := by
  classical
  let : Fintype I := Fintype.ofFinite _
  obtain ⟨ν, hν⟩ := exists_d4A2_zeroFace P b hspan e hD i j hij
  let η := P.coroot i + P.coroot j
  let n : ℤ := (∑ k : I, |P.root' k η|) + 1
  let f := n • ν + η
  let coord := d4CorootCoordinates P b hspan e
  let g₀ : Module.Dual ℤ Y := (dotProductBilin ℤ ℤ (coord η)).comp coord
  let g : Module.Dual ℤ Y := (dotProductBilin ℤ ℤ (coord f)).comp coord
  have hg₀ (k : I) : g₀ (P.coroot k) = P.root' k η :=
    (dotProduct_comm _ _).trans (d4CorootCoordinates_dotProduct_coroot P b hspan e hD k η)
  have hg (k : I) : g (P.coroot k) = P.root' k f :=
    (dotProduct_comm _ _).trans (d4CorootCoordinates_dotProduct_coroot P b hspan e hD k f)
  have hs (k l : I) : P.pairing k l = P.pairing l k := by
    change P.root' k (P.coroot l) = P.root' l (P.coroot k)
    rw [← d4CorootCoordinates_dotProduct_coroot P b hspan e hD k (P.coroot l),
      ← d4CorootCoordinates_dotProduct_coroot P b hspan e hD l (P.coroot k), dotProduct_comm]
  have hi : P.root' i η = 1 := by
    change P.root' i (P.coroot i + P.coroot j) = 1
    rw [map_add, show P.root' i (P.coroot i) = 2 from P.pairing_same i, show P.root' i (P.coroot j) = -1 from hij]
    decide
  have hj : P.root' j η = 1 := by
    change P.root' j (P.coroot i + P.coroot j) = 1
    rw [map_add, show P.root' j (P.coroot j) = 2 from P.pairing_same j,
      show P.root' j (P.coroot i) = -1 from (hs j i).trans hij]
    decide
  have hi₀ := (hν i).mpr (Or.inl rfl)
  have hj₀ := (hν j).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hn (k : I) : |P.root' k η| < n := by
    have := Finset.single_le_sum (s := Finset.univ) (f := fun l => |P.root' l η|)
      (fun l _ => abs_nonneg (P.root' l η)) (Finset.mem_univ k)
    dsimp only [n]
    omega
  have hposn : 0 < n := lt_of_le_of_lt (abs_nonneg _) (hn i)
  have hfval (k : I) : P.root' k f = n * P.root' k ν + P.root' k η := by
    simp [f]
  have hf₀ (k : I) (hk : P.root' k ν = 0) : P.root' k f = P.root' k η :=
    by simp only [hfval, hk, mul_zero, zero_add]
  have hneg (k : I) (hk : P.root' k ν < 0) : P.root' k f < 0 := by
    rw [hfval]
    have hk' : P.root' k ν ≤ -1 := by omega
    have h := mul_le_mul_of_nonneg_left hk' hposn.le
    have h' := le_abs_self (P.root' k η)
    linarith [hn k]
  have hf (k : I) : P.root' k f ≠ 0 := by
    rcases lt_trichotomy (P.root' k ν) 0 with hk | hk | hk
    · exact (hneg k hk).ne
    · rw [hf₀ k hk, ← hg₀]
      have h := (hν k).mp hk
      rcases h with h | h | h | h | h | h <;>
        rw [h] <;> simp only [map_add, map_neg, hg₀, hi, hj] <;> decide
    · rw [hfval]
      have hk' : 1 ≤ P.root' k ν := by omega
      have h := mul_le_mul_of_nonneg_left hk' hposn.le
      have h' := neg_abs_le (P.root' k η)
      exact ne_of_gt (by linarith [hn k])
  obtain ⟨B, hB⟩ := RootDatumCoweightFace.exists_base_support P f hf
  have hcB : (B.support : Set I) = baseOf P.coroot (g : Y →+ ℤ) :=
    hB.trans (RootDatumBase.baseOf_root_eq_baseOf_coroot P (P.flip.toLinearMap f) g hf
      (fun k => by rw [hg]; exact hf k)
      (fun k => (congrArg (fun z : ℤ => 0 < z) (hg k)).symm.to_iff))
  have hpos (k : I) (hk : k ∈ B.support) : 0 < g (P.coroot k) := by
    have h : k ∈ baseOf P.coroot (g : Y →+ ℤ) := hcB ▸ (show k ∈ (B.support : Set I) from hk)
    exact h.1
  have hi₁ : g (P.coroot i) = 1 := (hg i).trans ((hf₀ i hi₀).trans hi)
  have hj₁ : g (P.coroot j) = 1 := (hg j).trans ((hf₀ j hj₀).trans hj)
  have mem_of_value_one (k : I) (hk : g (P.coroot k) = 1) : k ∈ B.support := by
    change k ∈ (B.support : Set I)
    rw [hcB]
    refine ⟨by change 0 < g (P.coroot k); omega, fun a ha c hc h => ?_⟩
    change 0 < g (P.coroot a) at ha
    change 0 < g (P.coroot c) at hc
    have hv := congrArg g h
    rw [map_add, hk] at hv
    omega
  refine ⟨ν, B, hν, fun k hk => le_of_not_gt fun h => ?_, ?_⟩
  · have h' := hpos k hk
    rw [hg] at h'
    exact (hneg k h).not_gt h'
  · intro k
    constructor
    · rintro ⟨hk, hk₀⟩
      have h := hpos k hk
      rcases (hν k).mp hk₀ with h' | h' | h' | h' | h' | h'
      · exact Or.inl (P.coroot.injective h')
      · rw [h', map_neg, hi₁] at h
        omega
      · exact Or.inr (P.coroot.injective h')
      · rw [h', map_neg, hj₁] at h
        omega
      · have hbase : k ∈ baseOf P.coroot (g : Y →+ ℤ) :=
          hcB ▸ (show k ∈ (B.support : Set I) from hk)
        exact ((hbase.2 i (by change 0 < g (P.coroot i); omega)
          j (by change 0 < g (P.coroot j); omega) h').elim
          (P.flip.ne_zero i) (P.flip.ne_zero j)).elim
      · rw [h', map_neg, map_add, hi₁, hj₁] at h
        omega
    · rintro (h | h)
      · rw [h]
        exact ⟨mem_of_value_one i hi₁, hi₀⟩
      · rw [h]
        exact ⟨mem_of_value_one j hj₁, hj₀⟩

end Langlands.LinearAlgebra
