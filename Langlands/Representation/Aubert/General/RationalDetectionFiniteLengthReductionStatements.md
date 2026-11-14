# Reductions of Sharp finite length, zero detection and exactness detection

Module `Langlands.Representation.Aubert.General.RationalDetectionFiniteLengthReductionStatements`.
Author: Worker 29, with Worker 3640, who chose this block for the general
Aubert program (Task 3640). Each input set is the one used by a conditional
theorem already in the shared draft of the proof task for that conclusion:

- Sharp finite length: Worker 4216, Task 4216
  (`0da1c37e-a39a-42e1-b90d-135db6c6e5c3`), shared draft revision 1;
- zero detection: Worker 4193, Task 4193
  (`db02aabd-9901-4fae-9583-ec28c66aec3c`), shared draft revision 1, applying
  Worker 379's generic reduction;
- exactness detection: Worker 128 wrote it and Worker 4194 checked it, Task
  4194 (`d70a1edd-5a84-4b03-aecf-2818901809d4`), shared draft revision 2,
  applying Worker 499's generic reduction.

The module declares three propositions in
`Langlands.Aubert.General.RationalPointFamily`. Each is an implication
between whole published propositions. None is proved here. None proves its
conclusion, and none adds a premise to it: each conclusion is the unchanged
published target.

## `RationalSharpFiniteLengthReductionStatement`

```
DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
  DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
    RationalSharpFiniteLengthStatement.{u, v}
```

The conclusion is `RationalSharpFiniteLengthStatement`
(`RationalSharpConsequenceTargets`). For every finite-length smooth `E` with
carrier in `Type (max (u + 1) v)` and every `I`, the actual terminal cokernel
`E#` of the normalized standard complex has finite length. Aubert (1995)
needs this to state Corollaire 3.9 (a), printed p. 2189, in the Grothendieck
group of finite-length representations.

The two inputs are the dynamic prerequisite statements of
`PrerequisiteStatements`:

- `DynamicInductionFiniteLengthStatement`: for every nonarchimedean local
  field, connected reductive `G` and cocharacter `χ`, the actual normalized
  induction from `Z_G(χ)(F)` along `P(χ)(F)` preserves finite length (Renard,
  Lemme VI.6.2, printed p. 178, which is stated for an irreducible inducing
  representation and extends to finite length by exactness);
- `DynamicJacquetFiniteLengthStatement`: the actual normalized Jacquet
  functor along `P(χ)(F)` preserves finite length (Renard VI.6.4, printed
  p. 179).

Both inputs are taken at field universe `u` and carrier universe
`max (u + 1) v`. That is the carrier universe of the conclusion at `u, v`, so
no universe is lowered or raised. The conclusion keeps all its premises,
including `hOrder` and `hUc`; the inputs are not per-instance premises.

## `RationalSupportCategoryZeroDetectionReductionStatement`

```
RationalCuspidalJacquetFactorExtractionStatement.{u, v} →
  RationalSupportCategoryZeroDetectionStatement.{u, v}
```

The conclusion is `RationalSupportCategoryZeroDetectionStatement`
(`RationalSupportCategoryTargets`). A member of the actual support category
`Alg({I})` whose actual Jacquet modules `r_J` vanish along every associated
standard Levi `L_J` (with `L_J = n L_I n⁻¹` for an associating point `n`) is
zero. This is the case of one object of the
first sentence of the proof in the 1996 erratum, printed p. 4687: "Par
définition de la catégorie Alg({I}), l'exactitude de la suite (∗) est
équivalente à celle, pour tout I dans {I}, de la suite …".

The input is `RationalCuspidalJacquetFactorExtractionStatement`
(`RationalCuspidalJacquetFactorTarget`). If an irreducible Levi-cuspidal `τ`
of `L_J` is a subquotient of `r_J(π)`, where `π` is a subquotient of the
actual normalized induction of an irreducible Levi-cuspidal `σ` of `L_I`,
then some actual point `n` conjugates `L_J` to `L_I`, `I` and `J` are
root-associated through `n`, and `τ` is isomorphic to the conjugate of `σ` by
`n`. Its source is Renard, Proposition VI.5.3 (ii),
(iii), printed p. 173, as applied in the proof of Théorème VI.5.4, printed
p. 174.

The implication passes through the intermediate published proposition
`RationalSupportCategoryIrreducibleJacquetDetectionStatement`
(`RationalSupportCategoryTargets`): an irreducible member of `Alg({I})` has a
nonzero Jacquet module along some associated standard Levi. The published
theorem `rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`
(`RationalIrreducibleJacquetFactorDetection`, Worker 658) proves that
extraction implies irreducible detection. Task 4193's draft proves that
irreducible detection implies zero detection. That intermediate theorem
keeps its owner. This statement uses the extraction input because it is the
premise both routes end at.

## `RationalSupportCategoryExactnessDetectionReductionStatement`

```
RationalSupportCategoryZeroDetectionStatement.{u, v} →
  RationalSupportCategoryExactnessDetectionStatement.{u, v}
```

The conclusion is `RationalSupportCategoryExactnessDetectionStatement`
(`RationalSupportCategoryTargets`). A composable pair `f : A ⟶ B`,
`g : B ⟶ C` with `B` in `Alg({I})` is exact at `B` if and only if every
actual Jacquet functor `r_J` along an associated standard Levi sends it to a
pair exact at `r_J(B)`. The outer objects `A` and `C` are arbitrary smooth
representations. This is the
first sentence of the proof in the erratum, printed p. 4687, quoted above.

The input is the zero-detection target of the previous section. The two
targets have the same premises and pass the same families, decompositions
and association relation to their generic templates. Exactness detection
also implies zero detection (take `0 ⟶ E ⟶ 0`), so the input cannot be
dropped.

## Scope

All inputs and conclusions are the published propositions themselves,
quantified over the same actual setting:

- every nonarchimedean local field, including positive characteristic;
- every connected reductive group, with its actual maximal split torus,
  generic cocharacter and actual simple relative roots, including the empty
  set;
- the canonical `pointTopology` on rational points (the dynamic inputs use
  `rationalPointTopology` on their own groups, as published);
- field universe `u` and representation carriers in `max (u + 1) v`, with
  `u` and `v` independent.

No proposition restricts to split, quasisplit or characteristic-zero groups,
or to `GL`. No finite-length, admissibility, exactness or compact-limit
premise is added to a conclusion.

## Provenance

These are derived, internal statements. They make no new claim from the
literature. Their mathematical content is that of the cited sources through
the published targets, whose own Markdown records the source correspondence.
Aubert's Proposition 3.2 is not used. The routes of the conditional theorems
in the three shared drafts are as follows.

- Sharp finite length. `sharpFiniteLengthTarget_of_inductionJacquet`
  (`SharpFiniteLength`) embeds each degree of the complex in a finite
  product of the terms `i_J r_J E` and takes a quotient. The premise that
  every composite `i_J r_J` preserves finite length comes from
  `standardInductionJacquet_preservesFiniteLength_of_dynamic`
  (`RationalStandardFiniteLength`), which identifies standard subgroups with
  dynamic ones through `hStandard`.
- Zero detection. Take an irreducible subquotient of a nonzero member of
  `Alg({I})`. Irreducible detection gives a nonzero Jacquet module of it, and
  exactness of the Jacquet functor makes the Jacquet module of the member
  nonzero (`supportCategoryZeroDetection_of_irreducibleJacquetDetection`,
  `SupportCategoryReductions`).
- Exactness detection. Zero detection on the image of `f` gives `f ≫ g = 0`.
  Zero detection on the kernel of the map induced by `g` on the cokernel of
  `f` gives exactness
  (`ExactnessDetection.supportCategoryExactnessDetection_of_zeroDetection`,
  `SupportCategoryExactnessReduction`).

In the last two routes the compact-limit property of the standard unipotent
radicals is proved from `hStandard`
(`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`),
so it is not an input. The proofs belong to separate `lean.proof@1`
successor tasks. Statement review does not establish them.
