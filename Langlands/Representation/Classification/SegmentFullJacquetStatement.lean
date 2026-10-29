import Langlands.Representation.Classification.Segments
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Tensor.Finite

/-!
# Full cuspidal Jacquet modules of segment subrepresentations and quotients

Zelevinsky 1980, 3.1 and 9.1(*). For a segment `Δ = [ρ, ν^(m-1) ρ]` of cuspidal
rank `r`, every irreducible subrepresentation of the increasing segment induction
`i(ρ, νρ, …, ν^(m-1) ρ)` on `GL_{mr}` has normalized Jacquet module along the
uniform shape `(r, …, r)` equivalent to `ρ ⊗ νρ ⊗ … ⊗ ν^(m-1) ρ`, and every
irreducible quotient of the same induction has normalized Jacquet module
equivalent to `ν^(m-1) ρ ⊗ … ⊗ νρ ⊗ ρ`.

These are proposition definitions, not proofs.
-/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Zelevinsky 1980, 3.1: for every segment `Δ = [ρ, ν^(m-1) ρ]` of cuspidal rank
`r`, every actual supercuspidal representative `A` of `ρ` and every irreducible
subrepresentation `π` of `i(ρ, νρ, …, ν^(m-1) ρ)`, the normalized Jacquet module of
`π` along the uniform shape `(r, …, r)` is equivalent, as a representation of the
block Levi `GL_r × ⋯ × GL_r`, to `A ⊗ νA ⊗ … ⊗ ν^(m-1) A`. -/
def SegmentSubrepresentationFullJacquet : Prop :=
  letI := T.topology
  ∀ (Δ : Segment.{uV, uF} T)
    (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    Δ.base.IsRepresentedBy A → T.IsSegmentSubrepresentation Δ π →
      Nonempty (((T.normalizedJacquetFunctor
          (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)).obj π).representation.Equiv
        (FiniteTensor.externalSmoothObject
          (T.segmentFactors A.obj Δ.length Δ.rank_pos)).representation)

/-- Zelevinsky 1980, 9.1(*): for every segment `Δ = [ρ, ν^(m-1) ρ]` of cuspidal
rank `r`, every actual supercuspidal representative `A` of `ρ` and every irreducible
quotient `π` of `i(ρ, νρ, …, ν^(m-1) ρ)`, the normalized Jacquet module of `π` along
the uniform shape `(r, …, r)` is equivalent, as a representation of the block Levi
`GL_r × ⋯ × GL_r`, to `ν^(m-1) A ⊗ … ⊗ νA ⊗ A`. -/
def SegmentQuotientFullJacquet : Prop :=
  letI := T.topology
  ∀ (Δ : Segment.{uV, uF} T)
    (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    Δ.base.IsRepresentedBy A → T.IsSegmentQuotient Δ π →
      Nonempty (((T.normalizedJacquetFunctor
          (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)).obj π).representation.Equiv
        (FiniteTensor.externalSmoothObject
          (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos)).representation)

/-- Zelevinsky 1980, 3.1 and 9.1(*): both full cuspidal Jacquet formulas, for the
specified field and topology. -/
def SegmentFullJacquetFormula : Prop :=
  SegmentSubrepresentationFullJacquet.{uF, uV} F T ∧
    SegmentQuotientFullJacquet.{uF, uV} F T

end Langlands.Classification
