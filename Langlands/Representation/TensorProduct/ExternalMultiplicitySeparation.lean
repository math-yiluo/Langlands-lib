import Langlands.Representation.Smooth.SeparatingIntertwiners
import Langlands.Representation.Tensor.Finite
import Langlands.Representation.TensorProduct.MultiplicityCancellation
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-! Joint separation by external tensor products of multiplicity projections. -/

noncomputable section
set_option autoImplicit false

open _root_.Representation
open scoped TensorProduct

universe uI uG uV uW uM

namespace Langlands

/-- When each block is a local representation tensored with a trivial complement,
external tensor products of the coefficient projections separate the block tensor. -/
theorem hasSeparatingIntertwiners_external_of_multiplicity
    {I : Type uI} [Fintype I] {H : I → Type uG} [∀ i, Group (H i)]
    {V : I → Type uV} {W : I → Type uW} {M : I → Type uM}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {σ : ∀ i, Representation ℂ (H i) (V i)} {τ : ∀ i, Representation ℂ (H i) (W i)}
    (e : ∀ i, (σ i).Equiv ((τ i).tprod (Representation.trivial ℂ (H i) (M i)))) :
    HasSeparatingIntertwiners (FiniteTensor.external σ) (FiniteTensor.external τ) := by
  classical
  intro z hz
  let E := PiTensorProduct.congr (fun i => (e i).toLinearEquiv)
  let bW := fun i => Module.Free.chooseBasis ℂ (W i)
  let bM := fun i => Module.Free.chooseBasis ℂ (M i)
  let b := Basis.piTensorProduct (fun i => (bW i).tensorProduct (bM i))
  have hEz : E z = 0 := by
    apply b.repr.injective
    apply Finsupp.ext
    intro a
    rw [map_zero, Finsupp.zero_apply]
    let p := fun i => TensorMultiplicity.coefficient (τ i) (bM i) (a i).2
    let c := (Basis.piTensorProduct bW).coord (fun i => (a i).1)
    have hcoord : b.coord a = c.comp (FiniteTensor.externalMap p).toLinearMap := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro t
      change b.coord a (PiTensorProduct.tprod ℂ t) =
        c (FiniteTensor.externalMap p (PiTensorProduct.tprod ℂ t))
      rw [FiniteTensor.externalMap_tprod]
      change (Basis.piTensorProduct (fun i => (bW i).tensorProduct (bM i))).repr
          (PiTensorProduct.tprod ℂ t) a =
        (Basis.piTensorProduct bW).repr (PiTensorProduct.tprod ℂ (fun i => p i (t i))) _
      rw [Basis.piTensorProduct_repr_tprod_apply, Basis.piTensorProduct_repr_tprod_apply]
      refine Finset.prod_congr rfl fun i _ => ?_
      induction (t i) using TensorProduct.inductionOn with
      | tmul w m =>
          simp only [p, TensorMultiplicity.coefficient_apply,
            TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul, Finsupp.smul_apply]
          exact Module.Basis.tensorProduct_repr_tmul_apply (bW i) (bM i) w m (a i).1 (a i).2
      | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
    have hMap : FiniteTensor.externalMap p (E z) = 0 := by
      have h := hz (FiniteTensor.externalMap (fun i => (p i).comp (e i).toIntertwiningMap))
      rw [FiniteTensor.externalMap_comp] at h
      exact h
    change b.coord a (E z) = 0
    rw [hcoord, LinearMap.comp_apply]
    change c (FiniteTensor.externalMap p (E z)) = 0
    rw [hMap, map_zero]
  exact E.injective (hEz.trans E.map_zero.symm)

end Langlands
