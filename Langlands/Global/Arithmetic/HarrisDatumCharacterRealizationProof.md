# The Harris datum characters on a paired-place configuration

Worker 84. The module proves
`Langlands.Global.HarrisDatum.harrisDatumCharacterRealization_of_halfWeight`:

`CMHalfWeightCharacterStatement.{uE'} → HarrisDatumCharacterRealizationStatement.{uF, uE, uE', uL}`.

The exact target `Langlands.Global.HarrisDatumCharacterRealizationOfHalfWeightStatement`
(module `HenniartHarrisDatumReductionStatement`) is proved by the theorem
`Langlands.Global.harrisDatumCharacterRealizationOfHalfWeight`, which is this
implication.

The weight-one hypothesis is used only when `[E' : E]` is even. The proof adds
no other hypothesis or axiom; the inspected axioms are `propext`,
`Classical.choice` and `Quot.sound`. It uses the helper modules
`HarrisDatumArchimedean`, `HarrisDatumLocal` and `HarrisDatumAuxiliary`.

## Conjugation and places

- `complexConj_algebraMap`: for CM fields `E ⊆ E'`, complex conjugation of
  `E'` restricts to that of `E`. Both induce complex conjugation under one
  embedding of `E'` (`IsCMField.complexEmbedding_complexConj`), which is
  injective.
- `conjPlace_liesOver`: the conjugate of a place of `E'` above `v` lies above
  `conjPlace E v`.
- `ne_of_liesOver`: places above distinct places are distinct.

## The proof

Fix a configuration, a reciprocity family `e` with `NormalizedReciprocity F e`,
and `χ₀ : FieldCharacter F F'`.

1. **Places.** The configuration's list `P.v, c(P.v), Ps.v, c(Ps.v)` is
   pairwise distinct. By the two lemmas above, `S = {P.v', Ps.v'}` is disjoint
   from its image under conjugation of `E'`.
2. **Auxiliary character.** `exists_generalPosition_of_unitAgreement` gives
   `χs₀`.
3. **Regular character.** The published `cmRegularUnitPrescription` is
   applied to `K₀` (degree two and totally complex, from
   `IsSplitImaginaryQuadratic`), its embedding into `E'` through `E`, an
   embedding `τK` of `K₀`, the weights `regularWeights`, the set `S`, and the
   unit characters `unitCharacter P.v' φ χ₀` and `unitCharacter Ps.v' φs χs₀`.
   It gives `m > 0` and a conjugate-inverse `X` of type `m · regularWeights`,
   with distinct weights above `τK` and these unit components.
4. **Weight-one twist.** If `[E' : E]` is even, the hypothesis applied to
   `halfWeights` and `S` gives a conjugate-inverse `ψ`, unramified on `S`, of
   twisted type `halfWeights`. Then `IsAlgebraicAfterTwist 1 (X * ψ)`. If the
   degree is odd, `ψ = 1` and `IsAlgebraicAfterTwist 0 X`. In both cases this
   is `IsAlgebraicAfterTwist (([E' : E] − 1) % 2)`, and
   `isAlgebraicAfterTwist_of_mod_two` gives `[E' : E] − 1`.
5. **Datum.** Let `ξ = X * ψ`, `χ = ξ_{P.v'} ∘ φ⁻¹` and
   `χs = ξ_{Ps.v'} ∘ φs⁻¹`. The field conditions of `IsProposition48Datum`
   come from the configuration. Conjugate inverse is
   `isConjugateInverse_mul`. Relative regularity is
   `isRelativelyRegular_of_weights` with `weights_ne_of_distinct` and
   `halfWeight_component_eq` (or the trivial `ψ`). `P.HasComponent ξ χ` holds
   because the configuration's compatibility of `φ` with `P.isoTilde`
   identifies `y` with `φ x`; likewise for `Ps`.
6. **Units.** `finiteComponent_mul_eq` shows that `χ` agrees with `χ₀`, and
   `χs` with `χs₀`, on the units of canonical norm one. General position of
   `χs` then follows from step 2. The required agreement on units of
   `discreteValuation` one follows by `discreteValuation_eq_one_iff`.

The local components at `P` and `Ps` are prescribed only on units, as in the
statement.
