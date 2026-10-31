import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Smooth.FiniteLengthGrothendieck

/-!
# Canonical Grothendieck maps for the actual normalized parabolic functors

Unconditional proposition definitions asserting unique integer-linear maps on
the exact finite-length smooth Grothendieck groups, with existential finite-length
witnesses for the actual functor outputs. All ranks and block shapes are included.
The field and carrier universes are independent, with all carriers saturated at
`max uF uV`. These definitions do not prove the assertions.
-/

namespace Langlands.Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- In every rank and block shape there is a unique integer-linear map taking
each finite-length smooth Levi class to the class of its actual normalized
parabolic induction. Finite length of that output is part of the conclusion. -/
def NormalizedInductionGrothendieckStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n),
    ∃! i : B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier,
      ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
        (hA : A.HasFiniteLength),
        ∃ hOut : ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A).HasFiniteLength,
          i (B.finiteLengthClass F.Carrier A hA) =
            GeneralLinear.finiteLengthClass n F.Carrier
              ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A) hOut

/-- In every rank and block shape there is a unique integer-linear map taking
each finite-length smooth GL class to the class of its actual normalized Jacquet
module. Finite length of that output is part of the conclusion. -/
def NormalizedJacquetGrothendieckStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n),
    ∃! r : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
        B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier,
      ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hA : A.HasFiniteLength),
        ∃ hOut : ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A).HasFiniteLength,
          r (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
            B.finiteLengthClass F.Carrier
              ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A) hOut

/-- Both actual normalized parabolic functors have the stated unique maps on
the exact finite-length smooth Grothendieck groups. -/
def NormalizedParabolicGrothendieckStatement : Prop :=
  NormalizedInductionGrothendieckStatement.{uF, uV} F T ∧
    NormalizedJacquetGrothendieckStatement.{uF, uV} F T

end Langlands.Parabolic
