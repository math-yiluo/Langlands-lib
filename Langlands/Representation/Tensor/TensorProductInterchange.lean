import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Interchanging indexed and binary tensor products -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.FiniteTensor

variable {𝕜 I : Type*} [Field 𝕜]
  (V M : I → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  [∀ i, AddCommGroup (M i)] [∀ i, Module 𝕜 (M i)]

private def pairTensorMap :
    PiTensorProduct 𝕜 V ⊗[𝕜] PiTensorProduct 𝕜 M →ₗ[𝕜]
      PiTensorProduct 𝕜 (fun i => V i ⊗[𝕜] M i) :=
  TensorProduct.lift (PiTensorProduct.map₂ (fun i => TensorProduct.mk 𝕜 (V i) (M i)))

private theorem pairTensorMap_tprod (v : ∀ i, V i) (m : ∀ i, M i) :
    pairTensorMap V M (PiTensorProduct.tprod 𝕜 v ⊗ₜ[𝕜] PiTensorProduct.tprod 𝕜 m) =
      PiTensorProduct.tprod 𝕜 (fun i => v i ⊗ₜ[𝕜] m i) :=
  PiTensorProduct.map₂_tprod_tprod (fun i => TensorProduct.mk 𝕜 (V i) (M i)) v m

variable [Finite I]

private theorem pairTensorMap_bijective : Function.Bijective (pairTensorMap (𝕜 := 𝕜) V M) := by
  let v i := Module.Free.chooseBasis 𝕜 (V i)
  let m i := Module.Free.chooseBasis 𝕜 (M i)
  let b := (Basis.piTensorProduct v).tensorProduct (Basis.piTensorProduct m)
  let c := Basis.piTensorProduct (fun i => (v i).tensorProduct (m i))
  let e : ((∀ i, Module.Free.ChooseBasisIndex 𝕜 (V i)) ×
      (∀ i, Module.Free.ChooseBasisIndex 𝕜 (M i))) ≃
        (∀ i, Module.Free.ChooseBasisIndex 𝕜 (V i) × Module.Free.ChooseBasisIndex 𝕜 (M i)) :=
    { toFun := fun p i => (p.1 i, p.2 i)
      invFun := fun p => (fun i => (p i).1, fun i => (p i).2)
      left_inv := by intro p; cases p; rfl
      right_inv := by
        intro p
        funext i
        exact Prod.ext rfl rfl }
  have h : pairTensorMap V M = (b.equiv c e).toLinearMap := by
    apply b.ext
    intro p
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp only [b, c, Module.Basis.tensorProduct_apply', Basis.piTensorProduct_apply,
      pairTensorMap_tprod]
    rfl
  rw [h]
  exact (b.equiv c e).bijective

/-- Pair corresponding factors of two finite indexed tensors. -/
def pairTensorEquiv :
    (PiTensorProduct 𝕜 V ⊗[𝕜] PiTensorProduct 𝕜 M) ≃ₗ[𝕜]
      PiTensorProduct 𝕜 (fun i => V i ⊗[𝕜] M i) :=
  LinearEquiv.ofBijective (pairTensorMap V M) (pairTensorMap_bijective V M)

@[simp]
theorem pairTensorEquiv_tprod (v : ∀ i, V i) (m : ∀ i, M i) :
    pairTensorEquiv V M (PiTensorProduct.tprod 𝕜 v ⊗ₜ[𝕜] PiTensorProduct.tprod 𝕜 m) =
      PiTensorProduct.tprod 𝕜 (fun i => v i ⊗ₜ[𝕜] m i) :=
  pairTensorMap_tprod V M v m

variable {V M} {V' M' : I → Type*}
  [∀ i, AddCommGroup (V' i)] [∀ i, Module 𝕜 (V' i)]
  [∀ i, AddCommGroup (M' i)] [∀ i, Module 𝕜 (M' i)]

/-- The interchange commutes with independent linear maps on both families. -/
theorem pairTensorEquiv_map (a : ∀ i, V i →ₗ[𝕜] V' i) (b : ∀ i, M i →ₗ[𝕜] M' i)
    (t : PiTensorProduct 𝕜 V ⊗[𝕜] PiTensorProduct 𝕜 M) :
    pairTensorEquiv V' M' (TensorProduct.map (PiTensorProduct.map a) (PiTensorProduct.map b) t) =
      PiTensorProduct.map (fun i => TensorProduct.map (a i) (b i)) (pairTensorEquiv V M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod d y =>
        simp only [TensorProduct.smul_tmul_smul, map_smul,
          TensorProduct.map_tmul, PiTensorProduct.map_tprod, pairTensorEquiv_tprod]
      | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  | add t t' ht ht' => simp only [map_add, ht, ht']

end Langlands.FiniteTensor
