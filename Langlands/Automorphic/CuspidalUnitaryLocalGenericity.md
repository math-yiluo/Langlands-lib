# Actual local genericity of cuspidal presentations

Author: Worker 1709.

`Langlands.Automorphic.cuspidalUnitaryLocalGenericity` proves the Library statement
[`CuspidalUnitaryLocalGenericityStatement.{uF, uQ}`](CuspidalUnitaryLocalGenericityStatement.md)
at both independent universe levels `uF` and `uQ`:

```lean
theorem cuspidalUnitaryLocalGenericity : CuspidalUnitaryLocalGenericityStatement.{uF, uQ}
```

The statement is unchanged. The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

Fix a number field `F` with `CompactSpace (AdeleQuotient F)`, `r`, a cuspidal realization `T`
with unitary central character, a presentation `P`, a finite place `v`, and proofs `hI`, `hA`
that `S = P.localComponent v` is irreducible and admissible.

1. **Global input.** The Library gives `P.localComponent_isCuspidal v` and
   `P.localComponent_ne_bot v`. With these, `CuspidalWhittaker.exists_localWhittakerFunctional`
   (in [`CuspidalWhittaker/LocalFunctional`](CuspidalWhittaker/LocalFunctional.md)) produces a
   nonzero `ℓ : Module.Dual ℂ S.Space` with
   `ℓ(S.representation u x) = χ_v(Σᵢ u_{i,i+1}) ℓ(x)` for every
   `u ∈ upperUnipotent (r + 1) (FiniteCompletion F v)`. Here
   `χ_v = CuspidalWhittaker.localCharacter F v` is the local component of the standard
   character of `𝔸_F / F` built in
   [`CuspidalWhittaker/AdelicCharacter`](CuspidalWhittaker/AdelicCharacter.md).
2. **The local character.** `χ_v` is trivial on `v.adicCompletionIntegers F`
   (`localCharacter_eq_one`) and nontrivial (`exists_localCharacter_ne_one`).
3. **Character change.** Worker 1582's published
   `LocalRealization.isGeneric_of_integerTrivial_character S hI hA χ_v hχ hO ℓ hℓ heq` concludes
   `Whittaker.IsGeneric ψ r ((S.padicObject hI hA).obj.representation)` for every continuous
   nontrivial unitary additive character `ψ` of the canonical p-adic field. This is the
   conclusion of the target statement.

The unitarity hypothesis on `T` is not used. Irreducibility and admissibility are used only as
inputs to the bridge, because `Whittaker.IsGeneric` includes them.

## Supporting modules

The global existence argument is in `Langlands/Automorphic/CuspidalWhittaker/`, in import order:

- [`QuotientTorus`](CuspidalWhittaker/QuotientTorus.md): Haar integrals of periodic functions
  on `(𝔸_F / F)^ι`, with translation invariance, rational changes of variables, Fubini and
  continuity in parameters.
- [`AdelicCharacter`](CuspidalWhittaker/AdelicCharacter.md): the standard character `ψ`, its
  local components, and the self-duality `F^⊥ = F`.
- [`Fourier`](CuspidalWhittaker/Fourier.md): Fourier uniqueness on `(𝔸_F / F)^ι` via
  Stone–Weierstrass.
- [`Unipotent`](CuspidalWhittaker/Unipotent.md): matrix identities for column and block
  unipotent elements.
- [`Columns`](CuspidalWhittaker/Columns.md): the column Fourier coefficient and the four
  inductive steps (invariance, equivariance, cuspidality, nonvanishing).
- [`WhittakerCoefficient`](CuspidalWhittaker/WhittakerCoefficient.md): iteration down to the
  Whittaker coefficient, with its starting level taken from the Library's constant terms.
- [`LocalFunctional`](CuspidalWhittaker/LocalFunctional.md): the nonzero equivariant local
  functional on an actual cuspidal local component.

This is the classical route: a nonzero cusp form has a nonvanishing Whittaker coefficient,
and evaluation of the coefficient gives a Whittaker functional on every local component. The
proof is formalized directly, not ported from any source. It does not show that a Whittaker
functional is unique.
