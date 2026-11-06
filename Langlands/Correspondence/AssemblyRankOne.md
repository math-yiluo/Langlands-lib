# Rank-one compatibility of the Henniart assembly

This module proves the rank-one conjunct of
`Langlands.Correspondence.AssemblyOperationStatement`:

- `Langlands.Correspondence.rankOneCompatibility_of_assembly`: if
  `IsAssemblyOf F c0 c` and `SupercuspidalRankOneCompatibility F e c0`, then
  `RankOneCompatibility F e c`.

It needs neither the geometric normalization of `e` nor well-definedness of the
assembly: the computation uses the block decomposition and Langlands head that
`IsAssemblyOf` already supplies for the chosen rank-one parameter class.

## Mathematical content

In rank one the assembly reduces to the supercuspidal map. A Weil–Deligne
parameter of dimension one has one indecomposable block `σ ⊗ Sp(1)` with `σ` a
character, and the corresponding multisegment is the single segment `{[c0 σ]}` of
length one. Its Langlands head is `c0 σ` itself. In Henniart 2002
(`henniart-2002-characterization`), §2.9, printed p.596 (PDF p.10), the full map
satisfies `π(σ) = π_0(σ)` for irreducible `σ`, and a one-dimensional parameter is
irreducible. The Lean proof below implements the rank-one case directly; it does
not use the classification theorems.

## The implemented proof

Fix a quasi-character `χ`. The rank-one compatibility of `c0` gives an
irreducible Weil class `σ` of rank one, a representative `Aσ` of `σ` equivalent to
the Weil character of `χ`, and an automorphic representative `A'` of `c0 1 σ`
equivalent to `χ ∘ det`.

1. **The parameter class.** Choose a representative `A₀` of `σ` (continuous and
   irreducible, of rank one). `rankOneZeroMonodromyClass` is the class of
   `zeroMonodromy ν A₀`. It is a Frobenius-semisimple local parameter
   (`isLocalFrobeniusSemisimpleParameter_zeroMonodromy`): continuity of the
   pair follows from the third clause of the published
   `Weil.Local.localWeilContinuity`, and every endomorphism of a line is
   semisimple (`isSemisimple_of_finrank_eq_one`). `zeroMonodromyEquiv` turns the
   equivalence of `Aσ` with the Weil character into an equivalence of pairs, so
   this class `D` satisfies `IsRankOneParameterCharacter`.
2. **The block shape.** `IsAssemblyOf` gives `r`, `d`, `m`, `σ'`, an
   `IsBlockSum F σ' m D` and an `IsMultisegmentHeadClass` for `c 1 D`. Block
   `i` has dimension `(d i + 1)(m i + 1)` (`rank_block`), and dimensions add in
   direct sums (`rank_directSum`). A sum of positive products equal to one
   forces `r = 1` and `d 0 = m 0 = 0` (`blockShape_eq_of_sum_eq_one`,
   `isBlockSum_rankOne`).
3. **The Weil factor.** A block of length one is its Weil factor
   (`blockOneRepresentationEquiv`, through `K ⊗ (Fin 1 → K) ≅ K`), and a direct
   sum over `Fin 1` is its summand (`directSumUniqueRepresentationEquiv`). So the
   unique Weil factor `σ' 0` has the same underlying class as `A₀`
   (`weilClassForget_eq_of_isBlockSum`). Forgetting continuity and
   irreducibility is injective (`weilClassForget_injective`), so `σ' 0 = σ`.
4. **The multisegment.** With these data `multisegmentOf` is the singleton
   segment of `cuspidalDatumOf F c0 σ` (`multisegmentOf_rankOne`).
5. **The head.** `singletonSegment_isLanglandsHead_equiv` shows that a
   Langlands head `J` of a one-segment multisegment `{[ρ]}` is equivalent to the
   rank transport of any supercuspidal representative of `ρ`. Its proof unfolds
   `Multisegment.IsLanglandsHead`: the list of segments has length one; the
   segment-induced representation of a length-one segment is equivalent to the
   rank transport of its supercuspidal block (published
   `singletonSegmentInducedEquiv`) and hence irreducible; a one-block normalized
   product is its factor (published `singleBlockNormalizedProductEquiv`,
   followed by `castRankCompEquiv` for the rank reindexing); and an irreducible
   head of an irreducible representation is equivalent to it
   (`IsIrreducibleHead.nonempty_equiv_of_isIrreducible`: the surjection is
   nonzero, hence injective by Schur). Two representatives of the same
   supercuspidal class are isomorphic (`isoClass_eq_iff`), and
   `castRankCongrEquiv` transports that isomorphism.
6. **Conclusion.** Choose a supercuspidal representative `S` of `c0 1 σ`. It is
   equivalent to `A'` (`nonempty_equiv_of_supercuspidalToAutomorphic`, from the
   published `automorphicClassOf_eq_iff`). The head `J` of the assembly datum is
   equivalent to `S` by step 5 and to the automorphic representative `Ah` of
   `c 1 D`. Composing `χ ∘ det ≅ A' ≅ S ≅ J ≅ Ah` gives
   `IsRankOneCharacter F χ (c 1 D)`.

## Auxiliary declarations

- `Classification.IsIrreducibleHead.nonempty_equiv_of_isIrreducible`: an
  irreducible head of an irreducible representation is equivalent to it.
- `Representation.Equiv.compHom`: precomposing both sides of an equivalence with
  a group homomorphism.
- `PadicField.TopologicalData.castRankCongrEquiv`,
  `PadicField.TopologicalData.castRankCompEquiv`: rank transport respects
  equivalences, and a reindexed rank transport is a single rank transport.
- `PadicField.TopologicalData.singletonSegment_isLanglandsHead_equiv`: step 5.
- `WeilDeligneRepresentation.blockOneRepresentationEquiv`,
  `blockRepresentationEquivOfLengthOne`, `directSumUniqueRepresentationEquiv`:
  step 3.
- `Correspondence.weilClassForget_injective`,
  `isSemisimple_of_finrank_eq_one`,
  `isLocalFrobeniusSemisimpleParameter_zeroMonodromy`,
  `rankOneZeroMonodromyClass`, `parameterForget_rankOneZeroMonodromyClass`,
  `zeroMonodromyEquiv`, `blockShape_eq_of_sum_eq_one`, `isBlockSum_rankOne`,
  `weilClassForget_eq_of_isBlockSum`,
  `nonempty_equiv_of_supercuspidalToAutomorphic`, `multisegmentOf_rankOne`:
  steps 1–4 and 6.

These are internal lemmas derived for this proof; they are not statements of
the cited source.

The injectivity lemma `weilClassForget_injective` is reused from
`Langlands.Correspondence.RankOneComparison`.
