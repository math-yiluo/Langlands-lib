# Contragredients of Hecke twists

Author: Worker 5459, for Task 5826.

Module: `Langlands.Automorphic.HeckeTwist.ContragredientTwist`. It imports
`Langlands.Automorphic.Contragredient`, `Langlands.Automorphic.HeckeTwist.OperatorTwist` and
`Langlands.Automorphic.HeckeTwist.Admissibility`. It is a supporting module for the proof of
`Langlands.Automorphic.CuspidalContragredientExistenceStatement`
(`Langlands.Automorphic.CuspidalContragredientExistenceProof`). Like other
operator-realization files, it declares local `AddCommGroup` instances
(`Submodule.addCommGroup`) on the nested submodule spaces, and it sets
`backward.isDefEq.respectTransparency false`, as `HeckeTwist.OperatorTwist` does.
Declarations are in namespace `Langlands.Automorphic.OperatorRealization`.

## Main result

```lean
theorem IsContragredientOf.of_heckeDeterminantTwist
    (h : T.IsContragredientOf (S.heckeDeterminantTwist χ)) :
    (T.heckeDeterminantTwist χ).IsContragredientOf S
```

Here `S T : OperatorRealization F n` and `χ : HeckeCharacter F` is an arbitrary Hecke
character, which need not be unitary. `S.heckeDeterminantTwist χ` is the Library's actual
twist of `S` by `χ ∘ det` (the image of `S` under multiplication by `χ ∘ det`). The theorem
says: if `T` realizes the full-operator contragredient of the twist of `S`, then the twist of
`T` by the same character realizes the contragredient of `S`. Informally, if
`T ≅ (S ⊗ χ∘det)^∨`, then `T ⊗ χ∘det ≅ S^∨`. This is the standard identity
`(π ⊗ χ)^∨ ≅ π^∨ ⊗ χ⁻¹`, rearranged so that it uses twists by `χ` only.

## Proof

Write `e : S ≃ S ⊗ χ` and `e' : T ≃ T ⊗ χ` for the multiplication isomorphisms
`heckeDeterminantTwistEquiv`. Let `B₀` be the contragredient pairing between `S ⊗ χ` and `T`.
The new pairing is

`heckeTwistPairing χ B₀ (y, x) = B₀ (e y, e'⁻¹ x)`, for `y ∈ S` and `x ∈ T ⊗ χ`,

defined as `(B₀ ∘ₗ e).compl₂ e'⁻¹`. The six conditions of `IsContragredientPairing` are
proved as separate lemmas:

- `heckeTwistPairing_finite`, `heckeTwistPairing_compact`: invariance under finite adelic
  matrices `d` and the standard compact `k`. On both twists these act as on the original
  space times the same scalar `c = χ(det g)` (`heckeDeterminantTwistEquiv_finite`,
  `heckeDeterminantTwistEquiv_compact`). The generic lemma `pairing_twisted_invariant`
  shows that `c` occurs once in the first argument and is removed once from the second, so
  the two cancel.
- `heckeTwistPairing_lieAction`: Lie invariance. The real Lie action on a twist is the
  original action shifted by a scalar `a = heckeLieShift χ X`
  (`lieAction_heckeDeterminantTwistEquiv`). This uses
  `heckeDeterminantTwistEquiv_differential` and `ArchimedeanGL.envelopingShift_generator`:
  the character shift sends the enveloping generator `X` to `X + a`. Here `heckeLieShift`
  chooses that scalar through `exists_heckeEnvelopingShift_generator`. The generic lemma
  `pairing_shifted_invariant` shows that the shift appears with opposite signs in the two
  terms of `B(Xy, x) + B(y, Xx)`.
- `heckeTwistPairing_functional`: for each `x`, the functional `B(·, x)` is
  `B₀(·, e'⁻¹ x) ∘ e`. By `isContragredientFunctional_comp_heckeDeterminantTwistEquiv`, it is
  a contragredient functional of `S`. That lemma rests on
  `isContragredientFunctional_comp_of_twisted`: pulling back a functional along a linear map
  that intertwines up to scalars preserves the defining properties. The scalars for the
  finite group equal `1` on the open subgroup `heckeDeterminantKernel χ`, the kernel of
  `χ ∘ det` on finite adelic matrices (`finiteAdelicHeckeDeterminant_isOpen_ker`), so
  smoothness survives. The scalars for the compact group are nonzero, so the finite orbit
  span maps into a finite-dimensional space.
- `heckeTwistPairing_flip_injective` (generic `pairing_flip_injective`): injectivity of
  `x ↦ B(·, x)` follows from that of `B₀` because `e` and `e'` are bijective.
- `heckeTwistPairing_flip_surjective` (generic `pairing_flip_surjective`): take a
  contragredient functional `l` of `S`. By
  `isContragredientFunctional_comp_heckeDeterminantTwistEquiv_symm`, `l ∘ e⁻¹` is a
  contragredient functional of `S ⊗ χ`, so it equals `B₀(·, x₀)` for some `x₀`. Then
  `B(·, e' x₀) = l`.

The general lemmas `twist_symm_apply`, `twist_apply_symm`, `pairing_twisted_invariant`,
`pairing_shifted_invariant`, `pairing_flip_injective` and `pairing_flip_surjective` are
stated for arbitrary complex modules. Working with plain module types avoids expensive
definitional unfolding of the submodule spaces.

## Other declarations

- `heckeDeterminantKernel χ : OpenSubgroup (FiniteAdelicGL F n)` is the kernel of the finite
  part of `χ ∘ det`. `adelicDeterminant_ofFinite_eq_one` says `χ(det d) = 1` on this kernel.
- `heckeLieShift χ X : ℂ` and `heckeLieShift_spec` are described above.

This is derived content, not a transcription of a literature statement. It is the
contragredient-of-twist identity for the Library's concrete operator realizations.
