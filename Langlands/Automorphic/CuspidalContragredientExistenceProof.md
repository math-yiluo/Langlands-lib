# Existence of actual cuspidal contragredients without a unitary center: proof

Author: Worker 5459, for Task 5826.

Module: `Langlands.Automorphic.CuspidalContragredientExistenceProof`. Declaration:

```lean
theorem Langlands.Automorphic.cuspidalContragredientExistence :
    CuspidalContragredientExistenceStatement.{uF}
```

The theorem holds at an arbitrary universe level `uF`. It proves the Library statement
`Langlands.Automorphic.CuspidalContragredientExistenceStatement` (module
`Langlands.Automorphic.CuspidalContragredientExistenceStatement`), which is not modified.
The statement says: for every number field `F` with compact adele quotient, every `r` and
every actual cuspidal operator realization `T : CuspidalOperatorRealization F r` of
`GL_(r+1)`, there is `T' : CuspidalOperatorRealization F r` with
`T'.realization.IsContragredientOf T.realization`. No central-character hypothesis is made.
The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

The module imports the statement module, the published unitary case
`Langlands.Automorphic.CuspidalUnitaryContragredientExistenceProof`,
`HeckeTwist.FiniteSlice` and `HeckeTwist.FiniteLocalTransport`. It also imports two new
supporting modules submitted with this proof:

- `Langlands.Automorphic.IrreducibleCentralCharacterProof`: every irreducible operator
  realization has a unique central character
  (`OperatorRealization.existsUnique_hasCentralCharacter`).
- `Langlands.Automorphic.HeckeTwist.ContragredientTwist`: if `T` is a contragredient of the
  twist of `S` by `χ ∘ det`, then the twist of `T` by `χ ∘ det` is a contragredient of `S`
  (`OperatorRealization.IsContragredientOf.of_heckeDeterminantTwist`).

## Proof

Let `T` be cuspidal of rank `r + 1`.

1. **Central character.** `T.realization` is irreducible, so by
   `existsUnique_hasCentralCharacter` it has a central character `ω : HeckeCharacter F`.
   `ω` need not be unitary.
2. **Unitarizing twist.** Let `μ = unitarizingCharacter r ω`, the Hecke character
   `z ↦ ‖ω(z)‖ ^ (-1/(r+1))`. It is the composite of `ω` with the continuous character
   `unitsNormRpow s : ℂˣ →ₜ* ℂˣ`, `w ↦ ‖w‖ ^ s`, a real power regarded as a complex unit.
   Continuity comes from `Units.isEmbedding_val₀` and `Continuous.rpow_const` (the norm of a
   unit is nonzero). The twist `T.heckeDeterminantTwist μ` (Library, `HeckeTwist.OperatorTwist`)
   is again an actual cuspidal operator realization. Its central character is `μ ^ (r+1) * ω`:
   apply `OperatorRealization.toFiniteRealization_heckeDeterminantTwist`, then
   `FiniteRealization.heckeDeterminantTwist_hasCentralCharacter`. By
   `norm_unitarizingCharacter_pow_mul`, this character is unitary:
   `‖μ(z)‖^(r+1) · ‖ω(z)‖ = ‖ω(z)‖^(-1) · ‖ω(z)‖ = 1`. This is
   `hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter`.
3. **Unitary case.** The Library theorem `cuspidalUnitaryContragredientExistence` gives a
   cuspidal `T₀'` whose realization is a contragredient of the twist
   `T.realization.heckeDeterminantTwist μ`.
4. **Untwisting.** By `IsContragredientOf.of_heckeDeterminantTwist`, the realization of
   `T' = T₀'.heckeDeterminantTwist μ` is a contragredient of `T.realization`. `T'` is cuspidal
   because twisting preserves cuspidality and irreducibility.

## Auxiliary declarations (namespace `Langlands.Automorphic`)

- `unitsNormRpow (s : ℝ) : ℂˣ →ₜ* ℂˣ` and `norm_unitsNormRpow`:
  `‖unitsNormRpow s w‖ = ‖w‖ ^ s`.
- `unitarizingCharacter (r : ℕ) (ω : HeckeCharacter F) : HeckeCharacter F`, defined as
  `(unitsNormRpow (-1/(r+1))).comp ω`.
- `norm_unitarizingCharacter_pow_mul`: `‖(μ ^ (r+1) * ω)(z)‖ = 1`.
- `hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter`: the twist of a
  cuspidal realization with central character `ω` by `unitarizingCharacter r ω` satisfies
  `HasUnitaryCentralCharacter`.

The route follows the standard reduction from the general case to the unitary case: twist
by a power of the absolute value of the central character.
