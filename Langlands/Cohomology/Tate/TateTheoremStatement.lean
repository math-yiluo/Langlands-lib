import Langlands.Cohomology.Tate.CupDefinitions
import Mathlib.GroupTheory.Sylow

/-!
# Tate's cup-product theorem

Cup product on the left with a degree-two class whose restrictions to the Sylow
subgroups satisfy Tate's conditions is bijective in every integer Tate degree.
-/

open CategoryTheory

universe u

namespace Langlands.Tate

/-- Tate's theorem for the actual integral cup operation: if `a` restricts on every
Sylow subgroup to a generator of an `H²` of the subgroup's order and the
subgroup's `H¹` vanishes, then `a ∪ -` from `Ĥⁿ(G, ℤ)` to `Ĥⁿ⁺²(G, A)` is
bijective for every integer `n`. -/
def TateCupIsomorphism : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (A : Rep.{u} IntegralScalar.{u} G)
    (a : groupCohomology A 2),
    (∀ (p : ℕ), p.Prime → ∀ P : Sylow p G,
      Subsingleton (groupCohomology (Rep.res P.1.subtype A) 1) ∧
        Nat.card (groupCohomology (Rep.res P.1.subtype A) 2) = Nat.card P ∧
        AddSubgroup.zmultiples
            (groupCohomology.map P.1.subtype (𝟙 (Rep.res P.1.subtype A)) 2 a) = ⊤) →
    ∀ n : ℤ, Function.Bijective (integralH2Cup A n a)

end Langlands.Tate
