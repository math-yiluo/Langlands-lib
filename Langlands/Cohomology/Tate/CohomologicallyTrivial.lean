import Langlands.Cohomology.Tate.ZeroDefinitions

open CategoryTheory.Limits

universe u

namespace Langlands.Tate

/-- Every subgroup has zero actual Tate cohomology in every integer degree. -/
def IsCohomologicallyTrivial {R G : Type u} [CommRing R] [Group G] [Finite G]
    (A : Rep.{u} R G) : Prop :=
  ∀ (H : Subgroup G) [Fintype H], ∀ n : ℤ,
    IsZero (tateCohomology (Rep.res H.subtype A) n)

end Langlands.Tate
