import Langlands.Representation.Character.Basic
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Unitary.Basic

/-!
# Unitarity of constituents of a finite-length character limit

A derived form of Tadic 1986, Theorem 2.7(i), as used for the end-point clause
of Proposition 2.9. It uses the actual finite-rank distribution character and
actual smooth subquotients. This module states a proposition; it supplies no
proof of the character-limit assertion.
-/

namespace Langlands

open HarmonicAnalysis MeasureTheory Filter
open scoped Topology

universe uG uV

/-- If the actual distribution characters of irreducible admissible
unitarizable representations converge on every Schwartz--Bruhat test function
to the character of an admissible finite-length representation, every
irreducible actual subquotient of that limit is unitarizable. The group is
second countable, locally compact, Hausdorff and totally disconnected, and the
chosen regular Haar measure is also right invariant. -/
def UnitaryCharacterLimitSubquotientsStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [Measure.IsMulRightInvariant μ]
    (π : ℕ → SmoothRep.{0, uG, uV} ℂ G)
    (hπ : ∀ k, IsAdmissible (π k).representation)
    (ρ : SmoothRep.{0, uG, uV} ℂ G)
    (hρ : IsAdmissible ρ.representation),
    (∀ k, Representation.IsIrreducible (π k).representation) →
    (∀ k, IsUnitarizable (π k).representation) →
    SmoothRep.HasFiniteLength ρ →
    (∀ f : SchwartzBruhat G,
      Tendsto (fun k => Character.distribution μ (π k).representation (hπ k) f)
        atTop (𝓝 (Character.distribution μ ρ.representation hρ f))) →
    ∀ τ : SmoothRep.{0, uG, uV} ℂ G,
      Representation.IsIrreducible τ.representation →
      SmoothRep.IsSubquotient τ ρ →
      IsUnitarizable τ.representation

end Langlands
