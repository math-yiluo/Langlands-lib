import Langlands.WeilDeligne.Dual
import Langlands.WeilDeligne.SumsTensor
import Mathlib.LinearAlgebra.Contraction

/-! # Tensor duality of Weil–Deligne pairs -/

noncomputable section

namespace Langlands.WeilDeligneRepresentation

universe uK uG uV uW

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

section DualDistrib
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W] [Module.Finite K W]

/-- `l ⊗ m ↦ (x ⊗ y ↦ l x * m y)` intertwines tensors of transposes with the
transpose of the tensor. -/
theorem dualDistribEquiv_comp_map_dualMap (f : Module.End K V) (f' : Module.End K W) :
    (TensorProduct.dualDistribEquiv K V W).toLinearMap ∘ₗ
        TensorProduct.map f.dualMap f'.dualMap =
      (TensorProduct.map f f').dualMap ∘ₗ (TensorProduct.dualDistribEquiv K V W).toLinearMap := by
  apply TensorProduct.ext'
  intro l m
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    TensorProduct.dualDistribEquiv_tmul_tmul, LinearMap.dualMap_apply]

end DualDistrib

/-- On the underlying modules, `f ⊗ g ↦ (x ⊗ y ↦ g y * f x)` intertwines the tensor
of the negative-transpose operators with the negative transpose of the tensor
operator `a ⊗ 1 + 1 ⊗ b`. -/
theorem dualDistribEquiv_comp_monodromy {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K M] [Module.Finite K N]
    (a : Module.End K M) (b : Module.End K N) :
    (TensorProduct.dualDistribEquiv K M N).toLinearMap ∘ₗ
        (TensorProduct.map (-a.dualMap) 1 + TensorProduct.map 1 (-b.dualMap)) =
      (-(TensorProduct.map a 1 + TensorProduct.map 1 b).dualMap) ∘ₗ
        (TensorProduct.dualDistribEquiv K M N).toLinearMap := by
  apply TensorProduct.ext'
  intro f h
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearMap.add_apply, TensorProduct.map_tmul, map_add,
    LinearEquiv.coe_coe, TensorProduct.dualDistribEquiv_tmul_tmul, LinearMap.neg_apply,
    LinearMap.dualMap_apply, Module.End.one_apply]
  ring

/-- The tensor product of the dual pairs is equivalent to the dual of the tensor
product: `f ⊗ g` is sent to the functional `x ⊗ y ↦ g y * f x`. -/
def tensorDualEquiv (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    Equiv (tensor (dual A) (dual B)) (dual (tensor A B)) where
  representationEquiv :=
    Representation.Equiv.mk (TensorProduct.dualDistribEquiv K A B) (fun g => by
      apply TensorProduct.ext'
      intro f h
      apply TensorProduct.ext'
      intro x y
      rfl)
  comm_monodromy := dualDistribEquiv_comp_monodromy A.monodromy B.monodromy

/-- Zero monodromy commutes with duality, through the identity carrier map. -/
def dualZeroMonodromyEquiv (A : FiniteRepresentation.{uK, uG, uV} K G) :
    Equiv (dual (zeroMonodromy ν A)) (zeroMonodromy ν (FiniteRepresentation.dual A)) where
  representationEquiv := Representation.Equiv.refl _
  comm_monodromy := by
    change LinearMap.id ∘ₗ (-(0 : Module.End K A).dualMap) =
      (0 : Module.End K (Module.Dual K A)) ∘ₗ LinearMap.id
    ext l x
    simp

/-- Duality distributes over tensor products of pair classes. -/
theorem dualClass_tensorClass
    (X : IsomorphismClasses.{uK, uG, uV} K G ν) (Y : IsomorphismClasses.{uK, uG, uW} K G ν) :
    dualClass (tensorClass X Y) = tensorClass (dualClass X) (dualClass Y) := by
  induction X using Quotient.inductionOn with
  | h A =>
    induction Y using Quotient.inductionOn with
    | h B => exact Quotient.sound ⟨(tensorDualEquiv A B).symm⟩

end Langlands.WeilDeligneRepresentation
