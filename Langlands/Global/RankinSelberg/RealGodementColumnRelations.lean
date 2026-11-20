import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Continuation of relations among finite families of holomorphic sections -/

noncomputable section

open Filter Matrix Set
open scoped BigOperators Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

private theorem differentiable_det_entries {m : ℕ} (A : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i j, Differentiable ℂ (fun z => A z i j)) : Differentiable ℂ (fun z => (A z).det) := by
  simp only [Matrix.det_apply']
  exact Differentiable.fun_sum fun σ _ =>
    (Differentiable.fun_finsetProd fun i _ => hA (σ i) i).const_mul _

private theorem differentiable_adjugate_entries {m : ℕ} (A : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i j, Differentiable ℂ (fun z => A z i j)) (i j : Fin m) :
    Differentiable ℂ (fun z => (A z).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply differentiable_det_entries
  intro row col
  by_cases h : row = j
  · subst row
    simp only [Matrix.updateRow_self]
    exact differentiable_const _
  · simpa only [Matrix.updateRow_ne h] using hA row col

private theorem differentiable_dotProduct {m : ℕ} (x y : ℂ → Fin m → ℂ)
    (hx : ∀ i, Differentiable ℂ (fun z => x z i))
    (hy : ∀ i, Differentiable ℂ (fun z => y z i)) :
    Differentiable ℂ (fun z => dotProduct (x z) (y z)) :=
  Differentiable.fun_sum fun i _ => (hx i).mul (hy i)

/-- A relation between entire column families that implies equality of their
entire scalar values on an open set has the same implication wherever one
square family is a basis. -/
def RealGodementColumnRelationsStatement : Prop :=
  ∀ (m n : ℕ) (A : ℂ → Matrix (Fin m) (Fin m) ℂ) (B : ℂ → Matrix (Fin m) (Fin n) ℂ)
    (p : ℂ → Fin m → ℂ) (q : ℂ → Fin n → ℂ),
    (∀ i j, Differentiable ℂ (fun z => A z i j)) →
    (∀ i j, Differentiable ℂ (fun z => B z i j)) →
    (∀ i, Differentiable ℂ (fun z => p z i)) →
    (∀ i, Differentiable ℂ (fun z => q z i)) →
    ∀ z₀ : ℂ, (∀ᶠ z in 𝓝 z₀, ∀ (x : Fin m → ℂ) (y : Fin n → ℂ),
      A z *ᵥ x = B z *ᵥ y → dotProduct (p z) x = dotProduct (q z) y) →
    ∀ z : ℂ, (A z).det ≠ 0 → ∀ (x : Fin m → ℂ) (y : Fin n → ℂ),
      A z *ᵥ x = B z *ᵥ y → dotProduct (p z) x = dotProduct (q z) y

theorem realGodementColumnRelations : RealGodementColumnRelationsStatement := by
  intro m n A B p q hA hB hp hq z₀ hnear z hdet x y h
  let u := fun w : ℂ => B w *ᵥ y
  let v := fun w : ℂ => (A w).adjugate *ᵥ u w
  let L := fun w : ℂ => dotProduct (p w) (v w)
  let R := fun w : ℂ => (A w).det * dotProduct (q w) y
  have hu (i : Fin m) : Differentiable ℂ (fun w => u w i) :=
    differentiable_dotProduct (fun w => B w i) (fun _ => y) (hB i) (fun _ => differentiable_const _)
  have hv (i : Fin m) : Differentiable ℂ (fun w => v w i) :=
    differentiable_dotProduct (fun w => (A w).adjugate i) u (differentiable_adjugate_entries A hA i) hu
  have hL : Differentiable ℂ L := differentiable_dotProduct p v hp hv
  have hR : Differentiable ℂ R := (differentiable_det_entries A hA).mul
    (differentiable_dotProduct q (fun _ => y) hq (fun _ => differentiable_const _))
  have hLR : L =ᶠ[𝓝 z₀] R := hnear.mono fun w hw => by
    have hRange : A w *ᵥ v w = B w *ᵥ ((A w).det • y) := by
      change A w *ᵥ ((A w).adjugate *ᵥ (B w *ᵥ y)) = _
      rw [mulVec_mulVec, Matrix.mul_adjugate, smul_mulVec, one_mulVec, mulVec_smul]
    have hPoint := hw (v w) ((A w).det • y) hRange
    simpa only [L, R, dotProduct_smul, smul_eq_mul] using hPoint
  have hEq : L = R := AnalyticOnNhd.eq_of_eventuallyEq
    (fun w _ => hL.analyticAt w) (fun w _ => hR.analyticAt w) hLR
  have hvx : v z = (A z).det • x := by
    change (A z).adjugate *ᵥ (B z *ᵥ y) = _
    rw [← h, mulVec_mulVec, Matrix.adjugate_mul, smul_mulVec, one_mulVec]
  have hz : dotProduct (p z) (v z) = (A z).det * dotProduct (q z) y := congrFun hEq z
  rw [hvx, dotProduct_smul, smul_eq_mul] at hz
  exact mul_left_cancel₀ hdet hz

end Langlands.Global.RankinSelbergGlobal.RealGodement
