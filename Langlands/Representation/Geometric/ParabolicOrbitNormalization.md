# Actual orbit normalization cancellation

This internal prerequisite retains every prime, actual finite p-adic extension,
supplied compatible topology, minimal representative, and both complete
intersection-refinement triples. It proves identities on the full intermediate
group `parabolicOrbitStagesQuotient`, not only its refined Levi subgroup.

`parabolicOrbitSectionCharacter_halfBalance` says that the section character
(the product of the two positive source half moduli) times the coarse target
positive half modulus equals the refined target parabolic half modulus times
the actual correction-subgroup Haar character, embedded into the complex units.
The proof applies the published
`intersectionLeviHalfModulusBalance_sourceLevi` to the projected source and target
Levi coordinates. It identifies the correction normalizer there with the actual
stages correction normalizer on the projected section, then uses
`parabolicOrbitStagesCorrectionModulus_factor` to recover the character at the
original full intermediate element. The published
`refinedOuterHalfModulus_projection` identifies the coarse target half modulus.

`parabolicOrbitNormalizedSectionCharacter` is the product character of the target
inverse half, complex actual Haar ratio, and the section character.
`parabolicOrbitNormalization_cancel` proves, in the complex units,

```
target inverse half * complex(actual radical/correction Haar ratio)
  * section character = refined target parabolic half.
```

The actual radical character is identified with the explicit block modulus by
`parabolicOrbitStagesRadicalModulus`. The published `leviHalfModulus_sq` therefore
writes the complex Haar ratio as the square of the target positive half divided
by the actual correction character. Substituting the preceding half-balance and
cancelling units proves the identity.
`parabolicOrbitNormalizedSectionCharacter_eq` bundles this pointwise identity
as equality of the normalized scalar character with the refined target
parabolic half modulus pulled back along the actual stages equivalence. No Haar scaling, factorization, comparison,
or residual-twist premise is assumed. The proofs are internal consequences of
these published constructions; they introduce no additional source theorem.

This pair proves the scalar identities needed by orbit integration. The compact
induction comparison and the final natural normalized Jacquet isomorphism remain
separate obligations.
