# A Hecke determinant twist preserves a supercuspidal local component

`Langlands.Automorphic.heckeDeterminantTwistSupercuspidal` proves the published
[`HeckeDeterminantTwistSupercuspidalStatement`](HeckeDeterminantTwistDualitySupercuspidalStatement.md)
with independent universes `uE` for the number field and `uV` for the spectral
presentation's tensor carriers. For any presentation `P` of a cuspidal operator
realization at rank `r + 1` over `E` with `[CompactSpace (AdeleQuotient E)]`, the
actual twisted presentation `P.heckeDeterminantTwist ν` is supercuspidal at a
supplied finite place `v` if `P` is supercuspidal there. The Hecke character `ν`
is arbitrary; no CM, unitarity, or unramifiedness hypothesis is added.

## Proof

1. Unpack `LocalRealization.IsSupercuspidal` into irreducibility, admissibility,
   and a supercuspidal class `σ` whose image under `supercuspidalToAutomorphic`
   is the canonical p-adic class of `P.localComponent v`. The equivalences
   `heckeDeterminantTwist_localComponent_isIrreducible_iff` and
   `heckeDeterminantTwist_localComponent_isAdmissible_iff` in
   [`AssociatedGammaAutomorphicTwist`](AssociatedGammaAutomorphicTwist.md)
   supply the corresponding proofs for the twisted component.
2. Write `K` for `CompletionPadic.padicField v` and `χ` for the finite component
   `ν.finiteComponent v` in its `CompletionPadic.quasicharacterBase` form.
   `isCharacterTwist_heckeDeterminantTwist_padicClass` in the same module gives
   the ordinary character-twist relation between the original and twisted
   p-adic classes. The determinant character `χ ∘ det` has open kernel by
   `isOpen_ker_determinantQuasiCharacter` in
   [`SupercuspidalOperationRealization`](../Correspondence/SupercuspidalOperationRealization.md).
   Thus `Correspondence.isCharacterTwist_iff_eq_twist` identifies the twisted
   component's class with the `SmoothDualClass.twist` of the original class.
3. Use `Correspondence.supercuspidalTwist K χ σ` as the new supercuspidal class
   witness. `GeneralLinear.SupercuspidalClass.toSmoothDualClass_twist` in
   [`SupercuspidalTwist`](../Representation/Classification/SupercuspidalTwist.md)
   shows that forgetting supercuspidality commutes with the class twist. After
   rewriting by the two class equalities, this is precisely the required
   witness equation. Lean uses the canonical topology of `K` for this last
   lemma, matching the topology used to form the p-adic classes.

This is the class-level implementation of the published statement's
Jacquet-module argument. The existing supercuspidal class operation already
uses the fact that determinant characters are trivial on the unipotent
radicals that define those modules.
