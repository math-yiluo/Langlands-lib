# Rank one: the Artin conductor of a character of a finite extension is natural

Module `Langlands.LocalFactor.Ramification.RankOneConductorIntegrality`, namespace
`Langlands.Ramification.Padic`.

## Statement

For a prime `p`, a p-adic field `F` with valuation data `T`, and a field `K` between `ℚ_p` and
`F` (in any universe), every character `χ` of the automorphism group `F.Carrier ≃ₐ[K] F.Carrier`
has an Artin expression that is a natural number:

```lean
theorem Langlands.Ramification.Padic.exists_nat_artinConductor_rankOne.{uK, uL}
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) :
    ∃ a : ℕ, artinConductor T K (LocalClassField.rankOneCharacterRepresentation χ) = (a : ℚ)
```

`artinConductor T K` is the Library's rational sum `Σ_{i≥0} |G_i|/|G_0| · codim V^{G_i}` for the
action of `G = F.Carrier ≃ₐ[K] F.Carrier` on the integers of `F` (module
`Langlands.LocalFactor.Ramification.Galois`); `LocalClassField.rankOneCharacterRepresentation χ`
is the action of `G` on `ℂ` by `χ`. No Galois hypothesis is needed, and `K` and `F` have
independent universes.

## Proof

The statement is the first component of
`Langlands.Ramification.Padic.exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf`
(module `Langlands.LocalFactor.Ramification.Herbrand.CharacterExponentIntegrality`), which gives
natural Artin and Swan expressions for every character. That theorem computes the Swan expression
of `χ` as `Σ_{i≥1} |G_i|/|G_0| · [χ ≠ 1 on G_i]` and shows this sum is a natural number by the
Hasse–Arf theorem applied to the abelian quotient `G_0 / (G_0 ∩ ker χ)` of the lower filtration
(the `Langlands/AnthropicFLT` proof); the Artin expression is the Swan expression plus `1` or `0`
according as `χ` is non-trivial or trivial on inertia. No local class field theory is used.

## Declarations

- `exists_nat_artinConductor_rankOne` — the statement above.

## Use

The integrality proof (`Langlands.LocalFactor.Ramification.InducedRankOneDifference`) applies the
theorem over the fixed field `K_S` of a subgroup `S` of `Gal(F/K)`, to the character of
`Gal(F/K_S)` corresponding to a character of `S`.

## Sources

Serre, *Local Fields* (1979), Chapter VI §2 (literature ID `serre-1979-local-fields`): the
abelian case of Theorem 1′ (printed page 99), that the conductor of a character is a non-negative
integer, which is the Corollary to Proposition 5 (printed page 102), by the Hasse–Arf theorem
(Chapter IV §3, printed page 76, the place the Library's literature table gives; proved in
Chapter V, §7, Theorem 1, printed page 93). The page of `Herbrand/CharacterExponentIntegrality`
gives the details of that proof.
