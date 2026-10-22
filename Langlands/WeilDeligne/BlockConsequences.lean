import Langlands.WeilDeligne.BlockStatements

/-!
# Numerical consequences of the uncentered block operations

These proposition definitions supplement the published block identities with
explicit ranks, determinant characters and monodromy-kernel dimensions.
-/

noncomputable section

universe uK uG uV uW

namespace Langlands.WeilDeligneRepresentation.Blocks

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- Rank, determinant and top-weight kernel of a positive-length block. -/
def BlockNumericalConsequencesFor (ν : G →* Kˣ) : Prop :=
  ∀ (σ : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ), 0 < m →
    let B := block ν σ m
    B.rank = σ.rank * m ∧
    B.toFiniteRepresentation.determinantCharacter =
      σ.determinantCharacter ^ m * ν ^ (σ.rank * (m * (m - 1) / 2)) ∧
    Module.finrank K (LinearMap.ker B.monodromy) = σ.rank ∧
    Nonempty (FiniteRepresentation.Equiv B.kernelRepresentation
      (FiniteRepresentation.twist (ν ^ (m - 1)) σ))

/-- The dual block has the same rank, inverse determinant, and kernel the
untwisted dual Weil factor: the shifts `1-m` and `m-1` cancel. -/
def DualBlockConsequencesFor (ν : G →* Kˣ) : Prop :=
  ∀ (σ : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ), 0 < m →
    let D := dual (block ν σ m)
    D.rank = σ.rank * m ∧
    D.toFiniteRepresentation.determinantCharacter =
      (σ.determinantCharacter ^ m * ν ^ (σ.rank * (m * (m - 1) / 2)))⁻¹ ∧
    Module.finrank K (LinearMap.ker D.monodromy) = σ.rank ∧
    Nonempty (FiniteRepresentation.Equiv D.kernelRepresentation
      (FiniteRepresentation.dual σ))

/-- A character twist preserves rank and kernel dimension, twists the top
kernel, and multiplies the determinant by the character to the full block rank. -/
def TwistBlockConsequencesFor (ν : G →* Kˣ) : Prop :=
  ∀ (σ : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ) (χ : G →* Kˣ), 0 < m →
    let T := twist χ (block ν σ m)
    T.rank = σ.rank * m ∧
    T.toFiniteRepresentation.determinantCharacter =
      χ ^ (σ.rank * m) *
        (σ.determinantCharacter ^ m * ν ^ (σ.rank * (m * (m - 1) / 2))) ∧
    Module.finrank K (LinearMap.ker T.monodromy) = σ.rank ∧
    Nonempty (FiniteRepresentation.Equiv T.kernelRepresentation
      (FiniteRepresentation.twist (χ * ν ^ (m - 1)) σ))

/-- Tensor rank, determinant and monodromy-kernel dimension. Characteristic zero
is retained from the full block-tensor decomposition used in the derivation.
Either length may be zero. -/
def TensorBlockConsequencesFor [CharZero K] (ν : G →* Kˣ) : Prop :=
  ∀ (σ : FiniteRepresentation.{uK, uG, uV} K G)
    (τ : FiniteRepresentation.{uK, uG, uW} K G) (m n : ℕ),
    let T := tensor (block ν σ m) (block ν τ n)
    T.rank = (σ.rank * m) * (τ.rank * n) ∧
    T.toFiniteRepresentation.determinantCharacter =
      (σ.determinantCharacter ^ m *
        ν ^ (σ.rank * (m * (m - 1) / 2))) ^ (τ.rank * n) *
      (τ.determinantCharacter ^ n *
        ν ^ (τ.rank * (n * (n - 1) / 2))) ^ (σ.rank * m) ∧
    Module.finrank K (LinearMap.ker T.monodromy) =
      (σ.rank * τ.rank) * min m n

/-- The supplementary block-operation consequences, with independent universes
for the two Weil factors. No block identity is assumed as a hypothesis. -/
def BlockOperationConsequences : Prop :=
  (∀ (K : Type uK) [Field K] (G : Type uG) [Group G] (ν : G →* Kˣ),
    BlockNumericalConsequencesFor.{uK, uG, uV} ν ∧
    DualBlockConsequencesFor.{uK, uG, uV} ν ∧
    TwistBlockConsequencesFor.{uK, uG, uV} ν) ∧
  (∀ (K : Type uK) [Field K] [CharZero K] (G : Type uG) [Group G] (ν : G →* Kˣ),
    TensorBlockConsequencesFor.{uK, uG, uV, uW} ν)

end Langlands.WeilDeligneRepresentation.Blocks
