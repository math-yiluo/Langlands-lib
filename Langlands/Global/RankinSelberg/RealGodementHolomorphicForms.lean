import Langlands.Global.RankinSelberg.RealGodementColumnRelations

/-! # Holomorphic forms determined by spanning sections -/

noncomputable section

open Filter Matrix Set
open scoped BigOperators Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

universe u

private def formFromColumns {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (p : Fin m → ℂ) :
    (Fin m → ℂ) →ₗ[ℂ] ℂ where
  toFun x := A.det⁻¹ * dotProduct p (A.adjugate *ᵥ x)
  map_add' x y := by
    simp only [mulVec_add, dotProduct_add, mul_add]
  map_smul' c x := by
    change A.det⁻¹ * dotProduct p (A.adjugate *ᵥ (c • x)) =
      c * (A.det⁻¹ * dotProduct p (A.adjugate *ᵥ x))
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul, mul_left_comm]

private theorem formFromColumns_mulVec {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (p x : Fin m → ℂ)
    (hA : A.det ≠ 0) : formFromColumns A p (A *ᵥ x) = dotProduct p x := by
  change A.det⁻¹ * dotProduct p (A.adjugate *ᵥ (A *ᵥ x)) = _
  rw [mulVec_mulVec, Matrix.adjugate_mul, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hA, one_mul]

private theorem mulVec_adjugate_preimage {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ)
    (hA : A.det ≠ 0) : A *ᵥ (A.det⁻¹ • (A.adjugate *ᵥ x)) = x := by
  rw [mulVec_smul, mulVec_mulVec, Matrix.mul_adjugate, smul_mulVec, one_mulVec, smul_smul,
    inv_mul_cancel₀ hA, one_smul]

private theorem linearForm_mulVec {m n : ℕ} (L : (Fin m → ℂ) →ₗ[ℂ] ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) (p x : Fin n → ℂ)
    (h : ∀ j, L (fun i => A i j) = p j) : L (A *ᵥ x) = dotProduct p x := by
  have hx : A *ᵥ x = ∑ j : Fin n, x j • (fun i => A i j) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hx, map_sum, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, h, smul_eq_mul, mul_comm]

private theorem differentiable_det_of_entries {m : ℕ} (A : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i j, Differentiable ℂ (fun z => A z i j)) : Differentiable ℂ (fun z => (A z).det) := by
  simp only [Matrix.det_apply']
  exact Differentiable.fun_sum fun σ _ =>
    (Differentiable.fun_finsetProd fun i _ => hA (σ i) i).const_mul _

private theorem differentiableAt_formFromColumns {m : ℕ} (A : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (p : ℂ → Fin m → ℂ) (x : Fin m → ℂ)
    (hA : ∀ i j, Differentiable ℂ (fun w => A w i j)) (hp : ∀ j, Differentiable ℂ (fun w => p w j))
    (z : ℂ) (hz : (A z).det ≠ 0) : DifferentiableAt ℂ (fun w => formFromColumns (A w) (p w) x) z := by
  have hC (j : Fin m) : Differentiable ℂ (fun w => Matrix.cramer (A w) x j) := by
    simp only [Matrix.cramer_apply]
    apply differentiable_det_of_entries
    intro i k
    by_cases h : k = j
    · subst k
      simp only [Matrix.updateCol_self]
      exact differentiable_const _
    · simpa only [Matrix.updateCol_ne h] using hA i k
  have hN : Differentiable ℂ (fun w => dotProduct (p w) (Matrix.cramer (A w) x)) :=
    Differentiable.fun_sum fun j _ => (hp j).mul (hC j)
  have hD := (differentiable_det_of_entries A hA).differentiableAt.inv hz
  change DifferentiableAt ℂ (fun w => (A w).det⁻¹ * dotProduct (p w) ((A w).adjugate *ᵥ x)) z
  simp only [← Matrix.cramer_eq_adjugate_mulVec]
  exact hD.mul hN.differentiableAt

/-- Entire values on a spanning family of entire sections descend to an
entire family of linear forms if a linear form realizes them in one neighborhood. -/
def RealGodementHolomorphicFormsStatement : Prop :=
  ∀ (m : ℕ) (ι : Type u) (column : ι → ℂ → Fin m → ℂ) (value : ι → ℂ → ℂ),
    (∀ i j, Differentiable ℂ (fun z => column i z j)) → (∀ i, Differentiable ℂ (value i)) →
    (∀ z, ∃ b : Fin m → ι, (Matrix.of (fun i j => column (b j) z i)).det ≠ 0) →
    ∀ z₀ : ℂ, (∀ᶠ z in 𝓝 z₀, ∃ L : (Fin m → ℂ) →ₗ[ℂ] ℂ, ∀ i, L (column i z) = value i z) →
    ∃ L : ℂ → ((Fin m → ℂ) →ₗ[ℂ] ℂ),
      (∀ z i, L z (column i z) = value i z) ∧
      ∀ x, Differentiable ℂ (fun z => L z x)

theorem realGodementHolomorphicForms : RealGodementHolomorphicFormsStatement := by
  intro m ι column value hColumn hValue hBasis z₀ hNear
  let A := fun (b : Fin m → ι) (w : ℂ) => Matrix.of fun i j => column (b j) w i
  let row := fun (b : Fin m → ι) (w : ℂ) (j : Fin m) => value (b j) w
  have hA (b : Fin m → ι) (i j : Fin m) : Differentiable ℂ (fun w => A b w i j) := hColumn (b j) i
  have hRow (b : Fin m → ι) (j : Fin m) : Differentiable ℂ (fun w => row b w j) := hValue (b j)
  have hAt (b : Fin m → ι) (z : ℂ) (hd : (A b z).det ≠ 0) (i : ι) :
      formFromColumns (A b z) (row b z) (column i z) = value i z := by
    let B := fun w : ℂ => (Matrix.of fun j (_ : Fin 1) => column i w j : Matrix (Fin m) (Fin 1) ℂ)
    let q := fun w : ℂ => fun _ : Fin 1 => value i w
    have hRel : ∀ᶠ w in 𝓝 z₀, ∀ (x : Fin m → ℂ) (y : Fin 1 → ℂ),
        A b w *ᵥ x = B w *ᵥ y → dotProduct (row b w) x = dotProduct (q w) y :=
      hNear.mono fun w ⟨L, hL⟩ x y hxy => by
        rw [← linearForm_mulVec L (A b w) (row b w) x (fun j => hL (b j)),
          ← linearForm_mulVec L (B w) (q w) y (fun _ => hL i), hxy]
    let x := (A b z).det⁻¹ • ((A b z).adjugate *ᵥ column i z)
    have hRep : A b z *ᵥ x = column i z := mulVec_adjugate_preimage _ _ hd
    have hBrep : B z *ᵥ (1 : Fin 1 → ℂ) = column i z := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, B, Matrix.of_apply, Pi.one_apply, mul_one]
    have hEq := realGodementColumnRelations m 1 (A b) B (row b) q (hA b)
      (fun j k => hColumn i j) (hRow b) (fun _ => hValue i) z₀ hRel z hd x 1 (hRep.trans hBrep.symm)
    rw [← hRep, formFromColumns_mulVec _ _ _ hd, hEq]
    simp only [dotProduct, Fin.sum_univ_one, q, Pi.one_apply, mul_one]
  choose b hb using hBasis
  let L := fun z : ℂ => formFromColumns (A (b z) z) (row (b z) z)
  have hL (w : ℂ) (i : ι) : L w (column i w) = value i w := hAt (b w) w (hb w) i
  refine ⟨L, hL, fun x z => ?_⟩
  let c := b z
  have hD : Differentiable ℂ (fun w => (A c w).det) := differentiable_det_of_entries (A c) (hA c)
  have hz : (A c z).det ≠ 0 := hb z
  have hNonzero : ∀ᶠ w in 𝓝 z, (A c w).det ≠ 0 :=
    (isOpen_ne_fun hD.continuous continuous_const).mem_nhds hz
  have hEq : (fun w => L w x) =ᶠ[𝓝 z] (fun w => formFromColumns (A c w) (row c w) x) :=
    hNonzero.mono fun w hw => by
      let a := (A c w).det⁻¹ • ((A c w).adjugate *ᵥ x)
      have hRep : A c w *ᵥ a = x := mulVec_adjugate_preimage _ _ hw
      change L w x = formFromColumns (A c w) (row c w) x
      rw [← hRep, linearForm_mulVec (L w) (A c w) (row c w) a (fun j => hL w (c j)),
        formFromColumns_mulVec _ _ _ hw]
  exact (differentiableAt_formFromColumns (A c) (row c) x (hA c) (hRow c) z hz).congr_of_eventuallyEq hEq

end Langlands.Global.RankinSelbergGlobal.RealGodement
