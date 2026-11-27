import Langlands.Global.RankinSelberg.RealDiscreteLeviFourier
import Langlands.Representation.Archimedean.RealBlockJacquetFunctional
import Langlands.Representation.Archimedean.RealInducedStandardBound
import Langlands.Representation.Archimedean.RealLeviTorus

/-! # The compact angular estimate for real standard vectors -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviFourier

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open RealBlockFourierFinite RealBlockRotation RealInducedBlockBound
open RealLeviTorus (torusElem torusElem_mem_unitaryCompact)
open RealInducedStandardBound (slots inClass_slots exists_hasDegree)

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℝ

private theorem blockRotation_mul_torusElem {p : ℕ} (v : ℝ) :
    ∀ (L : List (Slot n)), (∀ t ∈ L, p + 1 < t.p ∨ t.p + 1 < p) →
      ∀ θ : Fin L.length → ℝ,
        blockRotation n p v * torusElem L θ = torusElem L θ * blockRotation n p v
  | [], _, _ => by simp [torusElem]
  | t :: L, h, θ => by
    simp only [torusElem]
    rw [← mul_assoc, blockRotation_mul_torusElem v L (fun s hs => h s (List.mem_cons_of_mem t hs)),
      mul_assoc, blockRotation_commute (h t List.mem_cons_self), ← mul_assoc]

private theorem torusElem_update : ∀ (L : List (Slot n)), L.Pairwise Slot.Disjoint →
    ∀ (θ : Fin L.length → ℝ) (i : Fin L.length) (v : ℝ),
      torusElem L (Function.update θ i v) =
        blockRotation n (L.get i).p v * torusElem L (Function.update θ i 0)
  | [], _, _, i, _ => i.elim0
  | t :: L, h, θ, i, v => by
    obtain ⟨ht, hL⟩ := List.pairwise_cons.mp h
    cases i using Fin.cases with
    | zero =>
      have htail (z : ℝ) : (fun i : Fin L.length => Function.update θ 0 z i.succ) =
          fun i : Fin L.length => θ i.succ := by
        funext i
        exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
      simp only [torusElem, Function.update_self, List.get_cons_zero, htail, blockRotation_zero, mul_one]
      exact (blockRotation_mul_torusElem v L ht _).symm
    | succ i =>
      have htail (z : ℝ) : (fun j : Fin L.length => Function.update θ i.succ z j.succ) =
          Function.update (fun j : Fin L.length => θ j.succ) i z := by
        funext j
        classical
        simp only [Function.update_apply, Fin.succ_inj]
      simp only [torusElem, htail, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      rw [torusElem_update L hL _ i v, mul_assoc]
      rfl

/-- A vector evaluated on the independent compact rotations of a list of discrete blocks. -/
def compactAngularProfile (L : List (Slot n)) (f : G → ℂ) (g : G) (θ : Fin L.length → ℝ) : ℂ :=
  f (torusElem L θ * g)

/-- The product angular estimate applies to the compact profile of a standard vector at
any list of its distinct nonzero-weight blocks, uniformly in the compact translate. -/
def RealDiscreteLeviCompactProfileStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (L : List (Slot n)), L.Pairwise Slot.Disjoint →
      (∀ t ∈ L, t ∈ slots ds n ∧ t.M ≠ 0) → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (R : ℝ), (∀ g ∈ unitaryCompact ℝ n, ‖f.val g‖ ≤ R) →
          ∀ g ∈ unitaryCompact ℝ n, ∀ s : Fin L.length → ℝ,
            let k (i : Fin L.length) := (L.get i).M
            let U := angularIntegrand k (compactAngularProfile L f.val g) s
            Integrable U ∧ ‖∫ x, U x‖ ≤ C * R * ∏ i, |s i| ^ ((k i : ℝ) / 2)

theorem realDiscreteLeviCompactProfile : RealDiscreteLeviCompactProfileStatement := by
  intro n ds f L hL hslots
  have hContinuous := RealBlockJacquet.continuous_coe f
  obtain ⟨D₀, hD₀⟩ := exists_hasDegree hContinuous f.2.2 (slots ds n)
  have hClass := inClass_slots f.2 hD₀
  choose D hD using fun i : Fin L.length =>
    exists_trigPoly_of_mem_kFiniteVectors (L.get i).hp hContinuous f.2.2
  let k (i : Fin L.length) := (L.get i).M
  have hk (i : Fin L.length) : k i ≠ 0 := (hslots _ (List.get_mem L i)).2
  obtain ⟨C, hC, hB⟩ := realDiscreteLeviFourierBound L.length k D hk
  refine ⟨C, hC, fun R hR g hg => hB (compactAngularProfile L f.val g) R ?_ ?_⟩
  · intro θ
    exact hR _ (mul_mem (torusElem_mem_unitaryCompact L θ) hg)
  · intro θ i
    let g₀ := torusElem L (Function.update θ i 0) * g
    have hg₀ : g₀ ∈ unitaryCompact ℝ n := mul_mem (torusElem_mem_unitaryCompact L _) hg
    have he : (fun v => compactAngularProfile L f.val g (Function.update θ i v)) =
        fun v => f.val (blockRotation n (L.get i).p v * g₀) := by
      funext v
      rw [compactAngularProfile, torusElem_update L hL, mul_assoc]
    rw [he]
    apply mem_angularSpace_of_trigPoly (hD i g₀ hg₀)
    intro j hj
    rw [← blockFourierCoefficient_eq_coeff]
    exact (hClass.2.2 _ (hslots _ (List.get_mem L i)).1).2.1 j hj g₀

end Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviFourier
