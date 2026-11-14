import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.Representation.Parabolic.InductionFactorMatchingStatement

/-!
# All-field port of `Langlands.Representation.Parabolic.InductionFactorMatchingStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.InductionFactorMatchingStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedInductionFactorMatchingTheorem NormalizedInductionOutputFiniteLength NormalizedInductionOutputMatching NormalizedInductionSourceMatching normalizedInductionObject
open Langlands.GeneralLinear
section Objects
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The actual normalized induced object, named so its covariant-function
carrier and module instances are shared in subsequent propositions. -/
noncomputable def normalizedInductionObject :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) →
      Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  fun σ => Rep.of (T.normalizedParabolicInduced B σ.representation)

/-- The existing multiplicity-sensitive matching of the actual source
representations, with no irreducibility or nonzeroness requirement. -/
def NormalizedInductionSourceMatching :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) →
      SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier) → Prop :=
  letI := T.topology
  fun σ τ =>
    HaveSameJordanHolderFactors (Rep.of σ.representation) (Rep.of τ.representation)

/-- Finite length over the ambient GL group algebra of the named actual
normalized induced object. -/
def NormalizedInductionOutputFiniteLength :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) → Prop :=
  letI := T.topology
  fun σ => IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
    (normalizedInductionObject T B σ).ρ.asModule

/-- The existing multiplicity-sensitive matching of the two named actual
normalized induced objects. -/
def NormalizedInductionOutputMatching :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) →
      SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier) → Prop :=
  letI := T.topology
  fun σ τ => HaveSameJordanHolderFactors
    (normalizedInductionObject T B σ) (normalizedInductionObject T B τ)

end Objects
/-- Normalized parabolic induction preserves matching of composition factors
with multiplicities when both actual induced representations have finite
group-module length. This proposition does not assert finite-length
preservation and is only a statement, not a proof. -/
def NormalizedInductionFactorMatchingTheorem.{uF, uV, uW} : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier)),
      NormalizedInductionSourceMatching T B σ τ →
      NormalizedInductionOutputFiniteLength T B σ →
      NormalizedInductionOutputFiniteLength T B τ →
      NormalizedInductionOutputMatching T B σ τ

end Langlands.AllFieldBZ.Parabolic
