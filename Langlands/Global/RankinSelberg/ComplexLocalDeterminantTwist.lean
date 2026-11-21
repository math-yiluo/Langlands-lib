import Langlands.Representation.Archimedean.ComplexStandardDeterminantTwist

/-! # Determinant twists of complex principal-series vectors -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ

/-- Multiply an inducing function by a character of the determinant. -/
def complexDeterminantTwist (d : ComplexCharacterData) (f : G → ℂ) (g : G) : ℂ :=
  (d.character (determinant g) : ℂ) * f g

variable (r) in
/-- A determinant character multiplies each inducing character of the
actual normalized complex principal series. -/
def ComplexLocalDeterminantTwistStatement : Prop :=
  ∀ (d : ComplexCharacterData) (χ : ℕ → ℂˣ → ℂ) (f : G → ℂ),
    f ∈ principalSeries ℂ n χ →
    complexDeterminantTwist d f ∈
      principalSeries ℂ n (fun i z => (d.character z : ℂ) * χ i z)

theorem complexLocalDeterminantTwist : ComplexLocalDeterminantTwistStatement r := by
  intro d χ f hf
  exact ComplexDeterminantTwist.detCharacter_mul_mem_principalSeries d.character
    (fun i z => mul_comm (d.character z : ℂ) (χ i z)) hf

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
