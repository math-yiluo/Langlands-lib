import Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
import Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
/-! Quasicuspidal prerequisites for the BZ77 cuspidal embedding theorem. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding CuspidalEmbeddingTheorem IrreducibleQuasicuspidalLeviAdmissibilityTheorem NormalizedQuasicuspidalEmbeddingTheorem ZeroRankCuspidalEmbeddingTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV

variable (F : Type uF) [Field F]
  (T : LocalFieldData F)

/-- The positive-rank embedding into actual normalized induction, with
quasicuspidal inducing data and no admissibility conclusion. -/
def NormalizedQuasicuspidalEmbeddingTheorem (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  0 < n →
    ∀ ω : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F),
      ω.IsIrreducible →
      ∃ (B : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F)),
        σ.IsIrreducible ∧ IsLeviQuasicuspidal B σ.representation ∧
        ∃ j : ω.representation.IntertwiningMap
            (Induction.smoothInduced (B.parabolic F)
              (twist (T.parabolicHalfModulus B)
                (σ.representation.comp (B.leviProjection F)))),
          Function.Injective j

/-- Irreducible smooth quasicuspidal representations of every actual product
Levi are admissible, including the empty product at rank zero. -/
def IrreducibleQuasicuspidalLeviAdmissibilityTheorem
    {n : ℕ} (B : BlockShape n) : Prop :=
  letI := T.topology
  ∀ σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
    σ.IsIrreducible → IsLeviQuasicuspidal B σ.representation → σ.IsAdmissible

/-- The elementary rank-zero boundary of the existing cuspidal embedding
target, with no additional hypotheses. -/
abbrev ZeroRankCuspidalEmbeddingTheorem : Prop :=
  CuspidalEmbeddingTheorem.{uF, uV} F T 0

end Langlands.AllField.CuspidalSupport
