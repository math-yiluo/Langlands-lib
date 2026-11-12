import Langlands.Representation.Smooth.RenardTensorSmoothProof
import Langlands.Representation.Smooth.RenardTwistEquivalenceProof
import Langlands.Representation.Smooth.RenardCoinvariantHeckeTensorProof

noncomputable section

open TensorProduct MeasureTheory

namespace Langlands.Renard.Smooth

open Langlands.Hecke Langlands.Algebra

universe u v w

namespace CoinvariantTensor

variable {G : Type u} [Group G]
variable {V : Type v} {W : Type w} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- An equivariant linear equivalence descends to the actual coinvariant quotients. -/
def coinvariantsEquiv (e : ρ.Equiv σ) :
    Representation.Coinvariants ρ ≃ₗ[ℂ] Representation.Coinvariants σ where
  toLinearMap := Representation.Coinvariants.map ρ σ e.toIntertwiningMap
  invFun := Representation.Coinvariants.map σ ρ e.symm.toIntertwiningMap
  left_inv x := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρ x
    change Representation.Coinvariants.mk ρ (e.symm (e v)) = _
    rw [e.symm_apply_apply]
  right_inv x := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective σ x
    change Representation.Coinvariants.mk σ (e (e.symm v)) = _
    rw [e.apply_symm_apply]

@[simp] theorem coinvariantsEquiv_mk (e : ρ.Equiv σ) (x : V) :
    coinvariantsEquiv e (Representation.Coinvariants.mk ρ x) =
      Representation.Coinvariants.mk σ (e x) := rfl

end CoinvariantTensor

/-- Renard III.1.15.1: the ordinary equivariant associator descends to Hecke tensors. -/
theorem heckeTensorAssociativity : HeckeTensorAssociativityStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ μ _ V W U _ _ _ _ _ _ ρ σ τ hρ hτ hρσ hστ Mρσ Mρ hMρσ hMρ
  obtain ⟨eL, hL⟩ := coinvariantHeckeTensor G μ (V ⊗[ℂ] W) U
    (Representation.tprod ρ σ) τ hρσ hτ Mρσ hMρσ
  obtain ⟨eR, hR⟩ := coinvariantHeckeTensor G μ V (W ⊗[ℂ] U)
    ρ (Representation.tprod σ τ) hρ hστ Mρ hMρ
  let a := CoinvariantTensor.coinvariantsEquiv (Representation.TensorProduct.assoc ρ σ τ)
  refine ⟨(eL.symm.trans a.toAddEquiv).trans eR, ?_⟩
  intro x y z
  change eR (a (eL.symm _)) = _
  rw [← hL (x ⊗ₜ y) z, eL.symm_apply_apply]
  exact hR x (y ⊗ₜ z)

/-- All five assertions of Renard III.1.14–III.1.15 on the published objects. -/
theorem renardCoinvariantTensorStatements : RenardCoinvariantTensorStatements.{u, v} :=
  ⟨tensorProductSmooth, checkRightActionExists, coinvariantHeckeTensor,
    heckeTensorAssociativity, twistEquivalence⟩

end Langlands.Renard.Smooth
