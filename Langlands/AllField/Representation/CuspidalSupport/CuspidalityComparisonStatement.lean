import Langlands.Representation.CuspidalSupport.CuspidalityComparisonStatement
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
/-! Comparison of standard Jacquet vanishing and the existing cuspidality predicates. -/

noncomputable section

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding SingleBlockCuspidalityClause
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) (n : ℕ)

/-- Pullback along the actual block diagonal embedding for a single block
identifies product-Levi cuspidality with GL supercuspidality. -/
def SingleBlockCuspidalityClause : Prop :=
  letI := T.topology
  ∀ (B : BlockShape n), B.length = 1 →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F) V),
      IsLeviCuspidal B (ρ.comp (B.leviEmbedding F)) ↔ IsSupercuspidal ρ

end Langlands.AllField.CuspidalSupport
