import Langlands.Representation.Character.ExactK0RealizationProof
import Langlands.Representation.Character.ExactK0InjectivityProof

/-! # The actual distribution character map on the exact finite-length K0 -/

noncomputable section

namespace Langlands.Character

open MeasureTheory

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure] [μG.Regular]
  (hAdm : ∀ (A : SmoothRep.{0, uG, uV} ℂ G), A.HasFiniteLength → A.IsAdmissible)

/-- The actual distribution character, extended over all short exact sequence
relations by the published realization theorem. -/
def exactK0DistributionCharacter :
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G →ₗ[ℤ]
      HarmonicAnalysis.Distribution G :=
  (exactK0CharacterRealization G μG hAdm).exists.choose

@[simp]
theorem exactK0DistributionCharacter_ofRepresentation
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength) :
    exactK0DistributionCharacter μG hAdm
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      distribution μG A.representation (hAdm A hA) :=
  (exactK0CharacterRealization G μG hAdm).exists.choose_spec A hA

/-- The published finite-family character independence theorem makes the actual
character map injective on the entire exact finite-length quotient. -/
theorem exactK0DistributionCharacter_injective :
    Function.Injective (exactK0DistributionCharacter μG hAdm) :=
  exactK0CharacterInjectivity G μG hAdm _ fun A hA =>
    exactK0DistributionCharacter_ofRepresentation μG hAdm A hA

include hAdm in
/-- For finite-length admissible objects, equality of genuine distribution
characters is equivalent to equality in the exact finite-length K0. -/
theorem ofRepresentation_eq_iff_distribution_eq
    (A B : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.HasFiniteLength) (hB : B.HasFiniteLength)
    (hAa : A.IsAdmissible) (hBa : B.IsAdmissible) :
    SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA =
        SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation B hB ↔
      distribution μG A.representation hAa = distribution μG B.representation hBa := by
  constructor
  · intro h
    simpa only [exactK0DistributionCharacter_ofRepresentation] using
      congrArg (exactK0DistributionCharacter μG hAdm) h
  · intro h
    apply exactK0DistributionCharacter_injective μG hAdm
    simpa only [exactK0DistributionCharacter_ofRepresentation] using h

end Langlands.Character
