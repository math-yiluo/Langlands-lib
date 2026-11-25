# Characters of subgroups extend

`Langlands/GaloisCohomology/Global/Selmer/Orthogonal.lean`, namespace `Langlands.GaloisCohomology`.

The orthogonal complements for pairings `A × B → ℚ/ℤ`, their counts, double orthogonals, and the sums
of pairings (`rightOrthogonal`, `leftOrthogonal`, `card_rightOrthogonal_mul_card`,
`leftOrthogonal_rightOrthogonal`, `bijective_of_pairing_eq_addEquiv`, `piPairing`, `prodPairing`, …)
are in the module `Langlands.Cohomology.Profinite.TorsionDual`. The count along an exact sequence of seven terms
(`card_mul_card_eq_of_exact_seven`) is in `Langlands.GaloisCohomology.Global.EulerCharacteristic.Corollaries`.
This file proves that characters of a subgroup extend (`surjective_restrictCharacter`).

```lean
theorem surjective_restrictCharacter (X : AddSubgroup A) :
    Function.Surjective fun χ : A →+ QZ => χ.comp X.subtype
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.surjective_restrictCharacter : ∀ {A : Type u_1} [inst : AddCommGroup A] (X : AddSubgroup A),
  Function.Surjective fun χ => AddMonoidHom.comp χ (AddSubgroup.subtype X)
```

## Outline of the proofs

- Extension of characters: `ℚ/ℤ` is divisible (`QZ.exists_comp_eq_of_injective`).


## Declarations

`surjective_restrictCharacter`.

## References

No source is cited: the statements are elementary facts on abelian groups and their characters.
