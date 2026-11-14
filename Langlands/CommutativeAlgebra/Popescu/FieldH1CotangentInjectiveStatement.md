# Injectivity of `H₁(L_{L/K}) ⊗_L M → H₁(L_{M/K})` for towers of fields

`Langlands.CommutativeAlgebra.Popescu.FieldH1CotangentInjectiveStatement` (universe `u`). For field
extensions `M/L/K` (`IsScalarTower K L M`), the `M`-linear map
`(Algebra.H1Cotangent.map K K L M).liftBaseChange M : M ⊗_L H₁(L_{L/K}) → H₁(L_{M/K})` is injective.

## Source

Stacks Project, More on Algebra, Lemma 15.35.2 (Tag 07E2), in the registered snapshots
`stacks-field-extension-cotangent-07E1-07E3-2026-11-14`: "Let `M/L/K` be field extensions. Then the
Jacobi-Zariski sequence
`0 → H₁(L_{L/K}) ⊗_L M → H₁(L_{M/K}) → H₁(L_{M/L}) → Ω_{L/K} ⊗_L M → Ω_{M/K} → Ω_{M/L} → 0`
is exact." This statement records the exactness at the left end, i.e. the injectivity of the first
map. The rest of the sequence is the Jacobi–Zariski sequence in Mathlib (`Algebra.H1Cotangent.δ`,
`KaehlerDifferential.exact_mapBaseChange_map`). The source proves the lemma from the vanishing of
`H₂` for field extensions (Lemma 15.34.7, Algebra Lemma 10.158.11).

## Encoding

- `H₁(L_{−})` is Mathlib's `Algebra.H1Cotangent` (`H¹` of the naive cotangent complex; Stacks Tag
  08RA). The first map of the sequence is the base change to `M` of the `L`-linear map
  `Algebra.H1Cotangent.map K K L M` induced by the square `K → L`, `K → M`. This is the same form as
  the Library's `Algebra.H1Cotangent.liftBaseChange_map_injective_of_smooth`, which proves it for
  smooth `L → M`.
- All fields are in one universe `u`.
