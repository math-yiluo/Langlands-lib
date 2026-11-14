import Langlands.AllFieldBZ.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
import Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem IrreducibleQuasicuspidalLeviAdmissibilityTheorem NormalizedQuasicuspidalEmbeddingTheorem ZeroRankCuspidalEmbeddingTheorem
open Langlands.GeneralLinear
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData)

/-- The positive-rank embedding into actual normalized induction, with
quasicuspidal inducing data and no admissibility conclusion. -/
def NormalizedQuasicuspidalEmbeddingTheorem (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  0 < n →
    ∀ ω : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      ω.IsIrreducible →
      ∃ (B : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
        σ.IsIrreducible ∧ IsLeviQuasicuspidal B σ.representation ∧
        ∃ j : ω.representation.IntertwiningMap
            (Induction.smoothInduced (B.parabolic F.Carrier)
              (twist (T.parabolicHalfModulus B)
                (σ.representation.comp (B.leviProjection F.Carrier)))),
          Function.Injective j

/-- Irreducible smooth quasicuspidal representations of every actual product
Levi are admissible, including the empty product at rank zero. -/
def IrreducibleQuasicuspidalLeviAdmissibilityTheorem
    {n : ℕ} (B : BlockShape n) : Prop :=
  letI := T.topology
  ∀ σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
    σ.IsIrreducible → IsLeviQuasicuspidal B σ.representation → σ.IsAdmissible

/-- The elementary rank-zero boundary of the existing cuspidal embedding
target, with no additional hypotheses. -/
abbrev ZeroRankCuspidalEmbeddingTheorem : Prop :=
  CuspidalEmbeddingTheorem.{uF, uV} F T 0

end Langlands.AllFieldBZ.CuspidalSupport
