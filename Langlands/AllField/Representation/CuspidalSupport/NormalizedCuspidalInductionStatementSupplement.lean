import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
/-! BZ77 cuspidal embedding, finite length, association, and Hom bounds. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding CuspidalInductionLengthTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV uW

variable (F : Type uF) [Field F]
  (T : LocalFieldData F) (n : ℕ)

/-- Irreducible cuspidal induction has finite group-module length and an
actual composition series with at most the factorial of the block count
many factors. -/
def CuspidalInductionLengthTheorem : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (B : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F)),
    σ.IsIrreducible → IsLeviCuspidal B σ.representation →
    let π := Induction.smoothInduced (B.parabolic F)
      (twist (T.parabolicHalfModulus B)
        (σ.representation.comp (B.leviProjection F)))
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F)) π.asModule ∧
      HasCompositionLengthAtMost (Rep.of π) (Nat.factorial B.length)

end Langlands.AllField.CuspidalSupport
