import Langlands.GroupScheme.AffineLinearEmbedding.Comodule
import Mathlib.RingTheory.Bialgebra.Hom

/-! # Coalgebra criteria for unipotence -/

noncomputable section

open Coalgebra TensorProduct

namespace Langlands.GroupScheme.CoalgebraUnipotence

variable {k : Type*} [Field k] {B : Type*}
  [Ring B] [Bialgebra k B]

/-- A multiplicative, counital matrix of coalgebra coefficients. -/
def IsCoefficientMatrix {n : ℕ} (a : Matrix (Fin n) (Fin n) B) : Prop :=
  (∀ i j, comul (R := k) (a i j) = ∑ l, a i l ⊗ₜ[k] a l j) ∧
  (∀ i j, counit (R := k) (a i j) = (1 : Matrix (Fin n) (Fin n) k) i j)

variable (k B)

/-- Every nonzero finite matrix corepresentation has a nonzero fixed vector. -/
def IsMatrixUnipotent : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a : Matrix (Fin n) (Fin n) B,
    IsCoefficientMatrix (k := k) a →
      ∃ v : Fin n → k, v ≠ 0 ∧ ∀ i, ∑ j, v j • a i j = v i • (1 : B)

/-- The common-kernel filtration for right translations by functionals vanishing at `1`. -/
def reducedLevel : ℕ → Submodule k B
  | 0 => ⊥
  | n + 1 =>
      ⨅ f : {f : Module.Dual k B // f 1 = 0},
        (reducedLevel n).comap (AffineLinearEmbedding.rightAct f.1)

/-- Every element is killed by all sufficiently long words of reduced right translations. -/
def IsLocallyConilpotent : Prop :=
  ∀ b : B, ∃ n : ℕ, b ∈ reducedLevel k B n

end Langlands.GroupScheme.CoalgebraUnipotence
