import Langlands.Representation.Character.Basic
import Langlands.Representation.Smooth.FiniteLengthGrothendieck
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Actual distribution characters and the exact finite-length Grothendieck group

Proposition targets for short-exact additivity, finite-family independence,
and realization and injectivity on the actual exact finite-length quotient.
The group and carrier universes remain independent. No target is proved here.
-/

namespace Langlands.Character

open MeasureTheory

universe uG uA uB uC uV

/-- Actual distribution characters are additive on every short exact sequence
of admissible smooth representations, including nonsplit sequences. The three
carriers have independent universes and need not be finite-dimensional. -/
def DistributionShortExactAdditivityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (A : SmoothRep.{0, uG, uA} ℂ G)
    (B : SmoothRep.{0, uG, uB} ℂ G)
    (C : SmoothRep.{0, uG, uC} ℂ G)
    (hA : A.IsAdmissible) (hB : B.IsAdmissible) (hC : C.IsAdmissible)
    (f : A.representation.IntertwiningMap B.representation)
    (g : B.representation.IntertwiningMap C.representation),
    SmoothRep.IsShortExact f g →
      distribution μ B.representation hB =
        distribution μ A.representation hA + distribution μ C.representation hC

/-- Bernstein--Zelevinsky (1976), Proposition 2.19: the actual distribution
characters of a finite family of pairwise inequivalent irreducible admissible
smooth representations are complex linearly independent. -/
def FiniteFamilyLinearIndependenceStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (r : ℕ) (A : Fin r → SmoothRep.{0, uG, uV} ℂ G)
    (hA : ∀ i, (A i).IsAdmissible),
    (∀ i, (A i).IsIrreducible) →
    Pairwise (fun i j => ¬ Nonempty ((A i).representation.Equiv (A j).representation)) →
      LinearIndependent ℂ (fun i => distribution μ (A i).representation (hA i))

/-- If every actual finite-length smooth representation in the selected carrier
universe is admissible, its actual distribution character extends uniquely to
an integer-linear map on the exact quotient by all short exact sequences. -/
def ExactK0CharacterRealizationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (hAdm : ∀ (A : SmoothRep.{0, uG, uV} ℂ G), A.HasFiniteLength → A.IsAdmissible),
    ∃! χ : SmoothRep.FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G →ₗ[ℤ]
        HarmonicAnalysis.Distribution G,
      ∀ (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength),
        χ (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
          distribution μ A.representation (hAdm A hA)

/-- Under the same generic admissibility premise, every integer-linear map with
all the actual finite-length generator values is injective on the whole exact
finite-length Grothendieck group, without resizing its carrier universe. -/
def ExactK0CharacterInjectivityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (hAdm : ∀ (A : SmoothRep.{0, uG, uV} ℂ G), A.HasFiniteLength → A.IsAdmissible)
    (χ : SmoothRep.FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G →ₗ[ℤ]
      HarmonicAnalysis.Distribution G),
    (∀ (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength),
      χ (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
        distribution μ A.representation (hAdm A hA)) →
      Function.Injective χ

end Langlands.Character
