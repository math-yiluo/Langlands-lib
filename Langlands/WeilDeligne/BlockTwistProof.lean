import Langlands.WeilDeligne.BlockStatements

/-!
# Twisting a block

The twist of `block ν σ m = σ ⊗ S_m` by a character `χ` and the block of the
twisted Weil factor `χ ⊗ σ` have the same carrier `σ ⊗ (Fin m → K)` and the same
monodromy `0 ⊗ 1 + 1 ⊗ N`; their actions `χ(g) • (σ(g) ⊗ S_m(g))` and
`(χ(g) • σ(g)) ⊗ S_m(g)` agree because the tensor product is bilinear. The
identity carrier map is therefore the required equivalence.
-/

noncomputable section

namespace Langlands.WeilDeligneRepresentation.Blocks

universe uK uG uV

open scoped TensorProduct

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- The identity carrier map from the twist of a block to the block of the
twisted Weil factor. -/
def blockTwistEquiv (ν χ : G →* Kˣ) (σ : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.twist χ (block ν σ m))
      (block ν (FiniteRepresentation.twist χ σ) m) where
  representationEquiv :=
    Representation.Equiv.mk (LinearEquiv.refl K (σ ⊗[K] (Fin m → K))) (fun g => by
      apply TensorProduct.ext'
      intro v w
      change (χ g : K) • (σ.representation g v ⊗ₜ[K] Special.action ν m g w) =
        ((χ g : K) • σ.representation g v) ⊗ₜ[K] Special.action ν m g w
      rw [TensorProduct.smul_tmul'])
  comm_monodromy := rfl

/-- Twisting a block twists its Weil factor and keeps its length. -/
theorem blockTwist : BlockTwist.{uK, uG, uV} :=
  fun _ _ _ _ ν χ σ m => ⟨blockTwistEquiv ν χ σ m⟩

end Langlands.WeilDeligneRepresentation.Blocks
