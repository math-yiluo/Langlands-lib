import Langlands.WeilDeligne.BlockStatements
import Langlands.WeilDeligne.DirectSumReindex
import Mathlib.LinearAlgebra.Pi

/-! # Block equivalences with independent carrier universes -/

noncomputable section

namespace Langlands.WeilDeligneRepresentation.Blocks

universe uK uG uV uW uι uκ

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}

open scoped TensorProduct

/-- Extend a Weil-factor equivalence across the special-block factor. -/
def blockEquivAcross {σ : FiniteRepresentation.{uK,uG,uV} K G}
    {τ : FiniteRepresentation.{uK,uG,uW} K G} (e : FiniteRepresentation.Equiv σ τ)
    (m : ℕ) : Equiv (block ν σ m) (block ν τ m) where
  representationEquiv := {
    toLinearEquiv := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl K (Fin m → K))
    isIntertwining' := by
      intro g
      change (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl K (Fin m → K))).toLinearMap ∘ₗ
        TensorProduct.map (σ.representation g) (Special.action ν m g) =
        TensorProduct.map (τ.representation g) (Special.action ν m g) ∘ₗ
          (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl K (Fin m → K))).toLinearMap
      apply TensorProduct.ext'
      intro v w
      change e (σ.representation g v) ⊗ₜ[K] Special.action ν m g w =
        τ.representation g (e v) ⊗ₜ[K] Special.action ν m g w
      exact congrArg (fun z => z ⊗ₜ[K] Special.action ν m g w)
        (LinearMap.congr_fun (e.isIntertwining' g) v) }
  comm_monodromy := by
    change (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl K (Fin m → K))).toLinearMap ∘ₗ
      (block ν σ m).monodromy = (block ν τ m).monodromy ∘ₗ
        (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl K (Fin m → K))).toLinearMap
    refine TensorProduct.ext' (fun (v : σ) (w : Fin m → K) => ?_)
    change (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl K (Fin m → K)))
        ((block ν σ m).monodromy (v ⊗ₜ[K] w)) =
      (block ν τ m).monodromy (e v ⊗ₜ[K] w)
    rw [block_monodromy_tmul, block_monodromy_tmul]
    rfl

/-- A matching of lengths and Weil factors induces an equivalence of sums. -/
theorem decompositionEquiv_of_matching (k l : ℕ)
    (d : Fin k → BlockDatum.{uK,uG,uV} K G)
    (d' : Fin l → BlockDatum.{uK,uG,uW} K G)
    (e : Fin k ≃ Fin l)
    (h : ∀ i, (d i).length = (d' (e i)).length ∧
      Nonempty (FiniteRepresentation.Equiv (d i).representation (d' (e i)).representation)) :
    Nonempty (Equiv (directSum fun i => (d i).pair ν)
      (directSum fun j => (d' j).pair ν)) := by
  refine ⟨(directSumCongr fun i => ?_).trans (directSumReindexEquiv e _).symm⟩
  change Equiv (block ν (d i).representation (d i).length)
    (block ν (d' (e i)).representation (d' (e i)).length)
  rw [← (h i).1]
  exact blockEquivAcross (h i).2.some _

end Langlands.WeilDeligneRepresentation.Blocks
