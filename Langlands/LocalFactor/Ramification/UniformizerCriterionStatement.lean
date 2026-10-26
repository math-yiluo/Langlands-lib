import Langlands.LocalFactor.Ramification.Galois
import Langlands.LocalField.RelativeIntegers

/-! # The uniformizer test for actual lower ramification groups -/

namespace Langlands.Ramification.Padic

universe u v

/-- Under surjectivity of the actual relative residue map, membership in a
nonnegative lower ramification group can be tested on any uniformizer.
This is a proposition target, not a proof. -/
def UniformizerCriterion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    Function.Surjective (PadicField.TopologicalData.relativeResidueMap T S) →
      ∀ (π : E.Carrier), S.ord π = 1 →
        ∀ (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (i : ℕ),
          σ ∈ lowerRamificationGroup S F.Carrier i ↔
            σ π - π = 0 ∨ (i + 1 : ℤ) ≤ S.ord (σ π - π)

end Langlands.Ramification.Padic
