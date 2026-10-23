import Mathlib.GroupTheory.Sylow
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

open CategoryTheory

universe u

namespace Langlands.Cohomology

/-- Positive-degree ordinary group cohomology is detected by restriction to Sylow subgroups. -/
def SylowDetection : Prop :=
  ∀ (k : Type u) [CommRing k] (G : Type u) [Group G] [Finite G]
    (A : Rep.{u} k G) (n : ℕ), 0 < n →
    ∀ x : groupCohomology A n,
      (∀ (p : ℕ), p.Prime → ∀ P : Sylow p G,
        groupCohomology.map P.1.subtype (𝟙 (Rep.res P.1.subtype A)) n x = 0) →
      x = 0

/-- Vanishing on all Sylow subgroups implies vanishing in positive-degree ordinary cohomology. -/
def SylowSubsingleton : Prop :=
  ∀ (k : Type u) [CommRing k] (G : Type u) [Group G] [Finite G]
    (A : Rep.{u} k G) (n : ℕ), 0 < n →
    (∀ (p : ℕ), p.Prime → ∀ P : Sylow p G,
      Subsingleton (groupCohomology (Rep.res P.1.subtype A) n)) →
    Subsingleton (groupCohomology A n)

end Langlands.Cohomology
