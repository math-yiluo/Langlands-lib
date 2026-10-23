import Langlands.Representation.Tensor.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homeomorph.Lemmas

/-! First-factor and singleton equivalences for dependent finite external tensors. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.FiniteTensor

universe uR uG uV

section Groups

variable {r : ℕ} (H : Fin (r + 1) → Type uG) [∀ i, Group (H i)]

/-- Separate the zeroth coordinate from the successor coordinates. -/
def headTail : (∀ i, H i) ≃* (H 0 × (∀ j : Fin r, H j.succ)) where
  toEquiv := (Fin.consEquiv H).symm
  map_mul' _ _ := rfl

@[simp]
theorem headTail_apply (g : ∀ i, H i) :
    headTail H g = (g 0, fun j : Fin r => g j.succ) := rfl

@[simp]
theorem headTail_symm_apply (g : H 0 × (∀ j : Fin r, H j.succ)) :
    (headTail H).symm g = Fin.cons g.1 g.2 := rfl

@[simp]
theorem headTail_symm_zero (g : H 0 × (∀ j : Fin r, H j.succ)) :
    (headTail H).symm g 0 = g.1 := rfl

@[simp]
theorem headTail_symm_succ (g : H 0 × (∀ j : Fin r, H j.succ)) (j : Fin r) :
    (headTail H).symm g j.succ = g.2 j := rfl

variable [∀ i, TopologicalSpace (H i)]

/-- The first-factor group equivalence for the ordinary product topologies. -/
def headTailContinuous : (∀ i, H i) ≃ₜ* (H 0 × (∀ j : Fin r, H j.succ)) where
  toMulEquiv := headTail H
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi (fun j => continuous_apply j.succ))
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd

@[simp]
theorem headTailContinuous_toMulEquiv :
    (headTailContinuous H).toMulEquiv = headTail H := rfl

@[simp]
theorem headTailContinuous_apply (g : ∀ i, H i) :
    headTailContinuous H g = (g 0, fun j : Fin r => g j.succ) := rfl

@[simp]
theorem headTailContinuous_symm_apply (g : H 0 × (∀ j : Fin r, H j.succ)) :
    (headTailContinuous H).symm g = Fin.cons g.1 g.2 := rfl

@[simp]
theorem headTailContinuous_symm_zero (g : H 0 × (∀ j : Fin r, H j.succ)) :
    (headTailContinuous H).symm g 0 = g.1 := rfl

@[simp]
theorem headTailContinuous_symm_succ (g : H 0 × (∀ j : Fin r, H j.succ)) (j : Fin r) :
    (headTailContinuous H).symm g j.succ = g.2 j := rfl

end Groups

section SingletonGroups

variable (H : Fin 1 → Type uG) [∀ i, Group (H i)]

/-- Evaluation at the unique coordinate as a group equivalence. -/
def evalOne : (∀ i, H i) ≃* H 0 := MulEquiv.piUnique H

@[simp]
theorem evalOne_apply (g : ∀ i, H i) : evalOne H g = g 0 := rfl

@[simp]
theorem evalOne_symm_zero (g : H 0) : (evalOne H).symm g 0 = g :=
  (evalOne H).apply_symm_apply g

/-- The inverse evaluation map, including the dependent coordinate transport. -/
theorem evalOne_symm_apply (g : H 0) (i : Fin 1) :
    (evalOne H).symm g i = (Subsingleton.elim (0 : Fin 1) i) ▸ g := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact evalOne_symm_zero H g

variable [∀ i, TopologicalSpace (H i)]

/-- Evaluation at zero for the ordinary product topology. -/
def evalOneContinuous : (∀ i, H i) ≃ₜ* H 0 where
  toMulEquiv := evalOne H
  continuous_toFun := (Homeomorph.piUnique H).continuous_toFun
  continuous_invFun := (Homeomorph.piUnique H).continuous_invFun

@[simp]
theorem evalOneContinuous_toMulEquiv :
    (evalOneContinuous H).toMulEquiv = evalOne H := rfl

@[simp]
theorem evalOneContinuous_apply (g : ∀ i, H i) : evalOneContinuous H g = g 0 := rfl

@[simp]
theorem evalOneContinuous_symm_zero (g : H 0) :
    (evalOneContinuous H).symm g 0 = g := evalOne_symm_zero H g

theorem evalOneContinuous_symm_apply (g : H 0) (i : Fin 1) :
    (evalOneContinuous H).symm g i = (Subsingleton.elim (0 : Fin 1) i) ▸ g :=
  evalOne_symm_apply H g i

end SingletonGroups

section Linear

variable (R : Type uR) [CommRing R] {r : ℕ}
variable (V : Fin (r + 1) → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Reindex zero and successors by a singleton and the tail. -/
private abbrev headTailIndex (r : ℕ) : PUnit.{1} ⊕ Fin r ≃ Fin (r + 1) :=
  ((Equiv.sumComm PUnit.{1} (Fin r)).trans
    (Equiv.optionEquivSumPUnit (Fin r)).symm).trans (finSuccEquiv r).symm

/-- Split off the first tensor factor, including an empty tail. -/
def headTailLinearEquiv :
    PiTensorProduct R V ≃ₗ[R] (V 0 ⊗[R] PiTensorProduct R (fun j : Fin r => V j.succ)) :=
  ((PiTensorProduct.reindex R V (headTailIndex r).symm).trans
    (PiTensorProduct.tmulEquivDep R (fun i => V (headTailIndex r i))).symm).trans
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv (R := R)
      (s := fun _ : PUnit.{1} => V 0) PUnit.unit) (LinearEquiv.refl R _))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem headTailLinearEquiv_tprod (v : ∀ i, V i) :
    headTailLinearEquiv R V (PiTensorProduct.tprod R v) =
      v 0 ⊗ₜ[R] PiTensorProduct.tprod R (fun j : Fin r => v j.succ) := by
  dsimp only [headTailLinearEquiv, LinearEquiv.trans_apply]
  rw [PiTensorProduct.reindex_tprod]
  have ht := PiTensorProduct.tmulEquivDep_symm_apply R
    (fun i => V (headTailIndex r i)) (fun i => v (headTailIndex r i))
  have hc := congrArg (TensorProduct.congr
    (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : PUnit.{1} => V 0)
      PUnit.unit) (LinearEquiv.refl R (PiTensorProduct R (fun j : Fin r => V j.succ)))) ht
  apply hc.trans
  change (TensorProduct.congr
    (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : PUnit.{1} => V 0)
      PUnit.unit) (LinearEquiv.refl R _))
    (PiTensorProduct.tprod R (fun _ : PUnit.{1} => v 0) ⊗ₜ[R]
      PiTensorProduct.tprod R (fun j : Fin r => v j.succ)) = _
  simp

@[simp]
theorem headTailLinearEquiv_symm_tmul (v : V 0) (w : ∀ j : Fin r, V j.succ) :
    (headTailLinearEquiv R V).symm (v ⊗ₜ[R] PiTensorProduct.tprod R w) =
      PiTensorProduct.tprod R (Fin.cons v w) := by
  apply (headTailLinearEquiv R V).injective
  simp

end Linear

section Actions

variable {R : Type uR} [CommRing R] {r : ℕ}
variable {H : Fin (r + 1) → Type uG} [∀ i, Group (H i)]
variable {V : Fin (r + 1) → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The first-factor linear splitting intertwines the pulled-back external action. -/
def headTailEquiv (ρ : ∀ i, Representation R (H i) (V i)) :
    Representation.Equiv ((external ρ).comp (headTail H).symm.toMonoidHom)
      (Representation.tprod ((ρ 0).comp (MonoidHom.fst _ _))
        ((external (fun j : Fin r => ρ j.succ)).comp (MonoidHom.snd _ _))) :=
  Representation.Equiv.mk (headTailLinearEquiv R V) (fun g => by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      external_tprod, headTailLinearEquiv_tprod, Representation.tprod_apply,
      TensorProduct.map_tmul, MonoidHom.coe_fst, MonoidHom.coe_snd,
      headTail_symm_zero, headTail_symm_succ])

@[simp]
theorem headTailEquiv_toLinearEquiv (ρ : ∀ i, Representation R (H i) (V i)) :
    (headTailEquiv ρ).toLinearEquiv = headTailLinearEquiv R V := rfl

/-- Intertwining on every tensor, with the coordinate actions displayed explicitly. -/
theorem headTailEquiv_apply_action (ρ : ∀ i, Representation R (H i) (V i))
    (g : H 0 × (∀ j : Fin r, H j.succ)) (x : PiTensorProduct R V) :
    headTailEquiv ρ (external ρ ((headTail H).symm g) x) =
      TensorProduct.map (ρ 0 g.1) (external (fun j : Fin r => ρ j.succ) g.2)
        (headTailEquiv ρ x) :=
  DFunLike.congr_fun ((headTailEquiv ρ).isIntertwining' g) x

@[simp]
theorem headTailEquiv_tprod (ρ : ∀ i, Representation R (H i) (V i)) (v : ∀ i, V i) :
    headTailEquiv ρ (PiTensorProduct.tprod R v) =
      v 0 ⊗ₜ[R] PiTensorProduct.tprod R (fun j : Fin r => v j.succ) :=
  headTailLinearEquiv_tprod R V v

@[simp]
theorem headTailEquiv_symm_tmul (ρ : ∀ i, Representation R (H i) (V i))
    (v : V 0) (w : ∀ j : Fin r, V j.succ) :
    (headTailEquiv ρ).symm (v ⊗ₜ[R] PiTensorProduct.tprod R w) =
      PiTensorProduct.tprod R (Fin.cons v w) :=
  headTailLinearEquiv_symm_tmul R V v w

end Actions

section SingletonActions

variable {R : Type uR} [CommRing R]
variable {H : Fin 1 → Type uG} [∀ i, Group (H i)]
variable {V : Fin 1 → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The singleton external action is its sole factor after evaluation pullback. -/
def singletonEquiv (ρ : ∀ i, Representation R (H i) (V i)) :
    Representation.Equiv ((external ρ).comp (evalOne H).symm.toMonoidHom) (ρ 0) :=
  Representation.Equiv.mk (PiTensorProduct.subsingletonEquiv (R := R) (s := V) 0)
    (fun g => by
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        external_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod,
        evalOne_symm_zero])

@[simp]
theorem singletonEquiv_toLinearEquiv (ρ : ∀ i, Representation R (H i) (V i)) :
    (singletonEquiv ρ).toLinearEquiv =
      PiTensorProduct.subsingletonEquiv (R := R) (s := V) 0 := rfl

/-- Intertwining for singleton evaluation on every tensor. -/
theorem singletonEquiv_apply_action (ρ : ∀ i, Representation R (H i) (V i))
    (g : H 0) (x : PiTensorProduct R V) :
    singletonEquiv ρ (external ρ ((evalOne H).symm g) x) = ρ 0 g (singletonEquiv ρ x) :=
  DFunLike.congr_fun ((singletonEquiv ρ).isIntertwining' g) x

@[simp]
theorem singletonEquiv_tprod (ρ : ∀ i, Representation R (H i) (V i)) (v : ∀ i, V i) :
    singletonEquiv ρ (PiTensorProduct.tprod R v) = v 0 :=
  PiTensorProduct.subsingletonEquiv_apply_tprod _ _

@[simp]
theorem singletonEquiv_symm_apply (ρ : ∀ i, Representation R (H i) (V i)) (v : V 0) :
    (singletonEquiv ρ).symm v =
      PiTensorProduct.tprod R (fun i => (Subsingleton.elim (0 : Fin 1) i) ▸ v) := by
  apply (singletonEquiv ρ).toLinearEquiv.injective
  change (PiTensorProduct.subsingletonEquiv (R := R) (s := V) 0)
      ((PiTensorProduct.subsingletonEquiv (R := R) (s := V) 0).symm v) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (singletonEquiv_tprod ρ
    (fun i => (Subsingleton.elim (0 : Fin 1) i) ▸ v)).symm

end SingletonActions

end Langlands.FiniteTensor
