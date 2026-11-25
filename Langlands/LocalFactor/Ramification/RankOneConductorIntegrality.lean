import Langlands.LocalFactor.Ramification.Herbrand.CharacterExponentIntegrality

/-!
# Rank one: the Artin conductor of a character of a finite extension is natural

For a finite extension `F/K` of p-adic fields and a character `χ` of `F.Carrier ≃ₐ[K] F.Carrier`,
the Artin expression of the one-dimensional representation of `χ` is a natural number
(`exists_nat_artinConductor_rankOne`). This is the rank-one input of the integrality proof in
`Langlands.LocalFactor.Ramification.FiniteIntegralityProof`. It is the Artin half of the
Library's `exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf`, which rests on the
Hasse–Arf theorem for abelian quotients of the lower filtration and uses no local class field
theory.
-/

namespace Langlands.Ramification.Padic

universe uK uL

/-- **Rank-one integrality.** A character of the automorphism group of a finite extension of
p-adic fields has a natural Artin conductor. -/
theorem exists_nat_artinConductor_rankOne {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) :
    ∃ a : ℕ, artinConductor T K (LocalClassField.rankOneCharacterRepresentation χ) = (a : ℚ) :=
  (exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf T K χ).1

end Langlands.Ramification.Padic
