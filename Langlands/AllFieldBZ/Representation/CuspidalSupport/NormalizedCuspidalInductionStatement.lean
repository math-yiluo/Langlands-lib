import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem
open Langlands.GeneralLinear
universe uF uV uW

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) (n : ℕ)

/-- Every irreducible smooth representation embeds in normalized induction
from an irreducible cuspidal representation of an actual standard Levi.
Admissibility is a conclusion, not an input. -/
def CuspidalEmbeddingTheorem : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ ω : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
    ω.IsIrreducible → ω.IsAdmissible ∧
    ∃ (B : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      σ.IsIrreducible ∧ IsLeviCuspidal B σ.representation ∧
      ∃ j : ω.representation.IntertwiningMap
          (Induction.smoothInduced (B.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus B)
              (σ.representation.comp (B.leviProjection F.Carrier)))),
        Function.Injective j

/-- Irreducible cuspidal induction has finite group-module length and an
actual composition series with at most the factorial of the block count
many factors. -/
def CuspidalInductionLengthTheorem : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (B : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    σ.IsIrreducible → IsLeviCuspidal B σ.representation →
    let π := Induction.smoothInduced (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        (σ.representation.comp (B.leviProjection F.Carrier)))
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) π.asModule ∧
      HasCompositionLengthAtMost (Rep.of π) (Nat.factorial B.length)

end Langlands.AllFieldBZ.CuspidalSupport
