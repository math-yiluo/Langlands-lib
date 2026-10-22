import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement

/-! Quasicuspidal prerequisites for the BZ77 cuspidal embedding theorem. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
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

/-- The three separately accessible prerequisites. Preservation of
admissibility by normalized induction remains the existing Parabolic clause. -/
def CuspidalEmbeddingPrerequisites : Prop :=
  (∀ n : ℕ, NormalizedQuasicuspidalEmbeddingTheorem.{uF, uV} F T n) ∧
  (∀ (n : ℕ) (B : BlockShape n),
    IrreducibleQuasicuspidalLeviAdmissibilityTheorem.{uF, uV} F T B) ∧
  ZeroRankCuspidalEmbeddingTheorem.{uF, uV} F T

end Langlands.CuspidalSupport
