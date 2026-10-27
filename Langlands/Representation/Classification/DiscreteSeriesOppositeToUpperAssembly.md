# Conditional assembly of the same-sigma opposite-to-upper comparison

Module `Langlands.Representation.Classification.DiscreteSeriesOppositeToUpperAssembly`.

**Scope.** The theorem `Langlands.glTemperedDiscreteSeriesOppositeToUpper_of`
proves the published target
`Langlands.GLTemperedDiscreteSeriesOppositeToUpperStatement.{uF,uV,uW}` from
five Library propositions, taken as **explicit hypotheses**. None of them is
proved here. As of this submission none has a published proof, so this is a
conditional, non-completing contribution. It is not the unconditional proof
the host task `5c6fcfcc-113f-4b4a-bf16-7008a7eeeb13` requires. The final proof
will apply this theorem to the five published proofs once they exist.

| Hypothesis | Proposition | Universes | Owning proof task |
| --- | --- | --- | --- |
| `h1` | `GLTemperedInductionStatement` (tempered upper induction: unitarizable, semisimple, tempered) | `{uF, uW}` | `fb462a13-96b1-4ac1-a47d-4fd7510d0ac4` |
| `h2` | `Parabolic.StandardSecondAdjointnessClause` | `{uF, uW, uV}` | `eb76bbde-911c-4875-9611-a11b9ba0300e` |
| `h3` | `GLTemperedDiscreteSeriesIsotypicStatement` (fixed-central isotypic projector) | `{uF, uV, uW}` | `1f2dda2f-d367-45eb-b840-80f0d253aac6` |
| `h4` | `GLTemperedOppositeJacquetScalarLayerStatement` (scalar layers of the opposite Jacquet module are tempered) | `{uF, uV, uV}` | `b1f2539d-c6fb-4358-b989-9a13c180521c` |
| `h5` | `Parabolic.IrreducibleOppositeJacquetFiniteLengthStatement` | `{uF, uV}` | `76126df1-ca14-4cd1-8f05-bf7014e4617c` |

In the target, `π` lives on `V : Type uV` and `σ` on `W : Type uW`. So
second adjointness is used with the Levi carrier in `uW` and the ambient
carrier in `uV`. The scalar-layer statement is used with both carriers in
`uV`, because the layers are subrepresentations of the Jacquet coinvariants of
`π`. The conclusion keeps `uF`, `uV`, `uW` independent.

No hypothesis is a version of the parent `GLTemperedDiscreteSeriesSummandStatement`,
the regular Langlands head, regular exhaustion, the square-integrable Langlands
classification, or tempered exhaustion. The contexts of the owning tasks of
`h3` and `h4` explicitly forbid those inputs.

## Proof

Fix the target data: `p`, `F`, `T`, positive `n`, `B`, a Borel Haar measure
`μ` on `M ⧸ Z(M)` with `M = B.Levi F.Carrier`, an irreducible tempered `π`, an
irreducible `σ` with `IsSquareIntegrableModCenter σ μ`, and an injective
intertwiner `π → T.normalizedOppositeParabolicInduced B σ`.

1. **σ is tempered.** The published `glLeviDiscreteSeriesTempered` gives
   `IsTemperedModCenter σ μ` for the same `μ`.
2. **Opposite semisimplicity** (first conclusion). Apply
   `isSemisimple_normalizedOppositeParabolicInduced_of_temperedInduction h1`
   from `OppositeReversalSemisimple`: block reversal plus `h1` at `B.reverse`.
3. **An irreducible quotient of the Jacquet module.** Let
   `J = OppositeSupport.jacquetAction T B π`, the actual opposite normalized
   Jacquet module. `π` is admissible (`IsTempered.isAdmissible`), hence smooth.
   The published opposite first adjointness
   `OppositeSupport.quotient_iff_embedding` turns the given embedding into a
   surjection `A : J → σ`.
4. **σ is a subrepresentation of J.** Apply
   `Langlands.exists_injective_of_scalarCentralSubs` (`ScalarSubReduction`)
   with `χ = cσ.character`, where `cσ` is the unitary central character that
   `hσSI` supplies. Finite length of `J` is `h5`. For the scalar-subrepresentation
   hypothesis, let `τ` be any representation of `M` (carrier in `uV`) with an
   injection `i : τ → J`, exact central action by `cσ.character`, and a
   surjection `q : τ → σ`.
   - Package the exact central action as a `UnitaryCentralCharacter τ` with the
     character of `cσ`.
   - `LinearEquiv.ofInjective` gives an equivariant inverse from the
     subrepresentation `i.range` of `J` onto `τ`. So `h4`, applied with
     `S = i.range`, gives `IsTemperedModCenter τ μ`.
   - `h3`, applied to `ρ = τ`, `σ` and the equal characters, gives an
     idempotent `P` whose range is the `σ`-isotypic supremum and whose kernel
     has no subrepresentation surjecting onto `σ`.
     `ScalarSubReduction.exists_injective_of_isotypicProjector` then gives an
     injection `σ → τ`.

   The result is an injective `f : σ → J`.
5. **A nonzero map from upper induction.** `h2` at `B` provides the linear
   equivalence
   `E : Hom(i_P (Rep.of σ), Rep.of π) ≃ Hom(Rep.of σ, oppositeJacquet T B (Rep.of π))`,
   using the admissibility of `σ` and `π`. The naturality equations are not
   needed. Its target is definitionally `Hom(σ, J)`. Set `g = E.symm f`. Then
   `g ≠ 0`, because `E g = f ≠ 0` (`W` is nontrivial since `σ` is
   irreducible). Since `π` is irreducible, `g` is surjective.
6. **Splitting** (second conclusion). The second component of `h1` at `B`,
   with the tempered `σ` from step 1, makes `T.normalizedParabolicInduced B σ`
   semisimple. `IsSemisimpleModule.lifting_property` applied to the surjection
   `g` on group-algebra modules gives `s : π → T.normalizedParabolicInduced B σ`
   with `g ∘ s = id`. So `s` is the required injective intertwiner.

Both inductions use the identical given `σ` on their actual function spaces.
Upper induction uses the positive half-modulus `T.parabolicHalfModulus B`;
opposite induction uses `T.oppositeParabolicHalfModulus B`, the inverse upper
half-modulus. Both act by right translation. The reversal in step 2 is used
only *inside* the semisimplicity argument; neither conclusion replaces `σ`.

## Provenance

This is a derived route. Silberger's Theorem 4.5.18 (printed p. 193, PDF
p. 199, `silberger-1979-harmonic-analysis`) has an equivalence for an
irreducible tempered `π`: occurrence of a square-integrable `ω` as a quotient
of the opposite Jacquet module, and occurrence of `π` as a summand of both
completely reducible inductions. Its proof follows Theorem 3.3.1 (printed
pp. 126-127, PDF pp. 132-133), with the auxiliary module required to be
tempered. Here the corresponding tempered auxiliary modules are the
scalar-character subrepresentations `τ` in step 4, whose temperedness is `h4`.
The splitting of their coefficient algebra is `h3`. Second adjointness (`h2`)
replaces the source's direct comparison of the two inductions. The complete
reducibility of the inductions (Silberger, Lemma 4.5.15, printed p. 191) is
`h1` together with the reversal.
