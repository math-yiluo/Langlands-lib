import Langlands.GroupScheme.CoalgebraUnipotence.Statements

universe u v w

noncomputable section

open Coalgebra TensorProduct
open Langlands.GroupScheme.AffineLinearEmbedding

namespace Langlands.GroupScheme.CoalgebraUnipotence

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Bialgebra k B]
  {C : Type*} [Ring C] [Bialgebra k C]

@[simp] theorem mem_reducedLevel_zero (b : B) :
    b ∈ reducedLevel k B 0 ↔ b = 0 := by
  simp [reducedLevel]

theorem mem_reducedLevel_succ (n : ℕ) (b : B) :
    b ∈ reducedLevel k B (n + 1) ↔
      ∀ f : Module.Dual k B, f 1 = 0 → rightAct f b ∈ reducedLevel k B n := by
  simp [reducedLevel, Submodule.mem_iInf, Submodule.mem_comap]

theorem reducedLevel_le_succ (n : ℕ) :
    reducedLevel k B n ≤ reducedLevel k B (n + 1) := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    intro b hb
    rw [mem_reducedLevel_succ] at hb ⊢
    exact fun f hf => ih (hb f hf)

theorem reducedLevel_mono : Monotone (reducedLevel k B) :=
  monotone_nat_of_le_succ reducedLevel_le_succ

theorem map_rightAct (q : B →ₐc[k] C) (f : Module.Dual k C) (b : B) :
    q (rightAct (f ∘ₗ (q : B →ₗ[k] C)) b) = rightAct f (q b) := by
  have h : ∀ t : B ⊗[k] B,
      q (TensorProduct.rid k B ((f ∘ₗ (q : B →ₗ[k] C)).lTensor B t)) =
        TensorProduct.rid k C
          (f.lTensor C (TensorProduct.map (q : B →ₗ[k] C) (q : B →ₗ[k] C) t)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [rightAct_apply, h, CoalgHomClass.map_comp_comul_apply, rightAct_apply]

theorem map_mem_reducedLevel (q : B →ₐc[k] C) (n : ℕ) {b : B}
    (hb : b ∈ reducedLevel k B n) : q b ∈ reducedLevel k C n := by
  induction n generalizing b with
  | zero =>
    have hb0 : b = 0 := (mem_reducedLevel_zero b).mp hb
    simp [hb0]
  | succ n ih =>
    rw [mem_reducedLevel_succ] at hb ⊢
    intro f hf
    rw [← map_rightAct q f b]
    exact ih (hb (f ∘ₗ (q : B →ₗ[k] C)) (by simpa using hf))

theorem isLocallyConilpotent_of_surjective (q : B →ₐc[k] C)
    (hq : Function.Surjective q) (hB : IsLocallyConilpotent k B) :
    IsLocallyConilpotent k C := by
  intro c
  obtain ⟨b, rfl⟩ := hq c
  obtain ⟨n, hn⟩ := hB b
  exact ⟨n, map_mem_reducedLevel q n hn⟩

theorem conilpotenceQuotient : ConilpotenceQuotientStatement.{u, v, w} := by
  intro k _ B _ _ C _ _ q hq hB
  exact isLocallyConilpotent_of_surjective q hq hB

end Langlands.GroupScheme.CoalgebraUnipotence
