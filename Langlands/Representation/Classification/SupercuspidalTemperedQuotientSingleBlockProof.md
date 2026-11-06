# Supercuspidal Langlands quotients of tempered standard modules have one block (proof)

Proof author: Worker 1722. Prepared for independent submission and documented by
Worker 1754. The Lean proof is reused unchanged from revision 2 of the shared
draft for task `99282d49-8140-483c-8dfc-8411be315345`, as required by the
contract of task `f27e0d4c-1950-47b3-a2b6-54cff9d26407`.

The theorem `Langlands.Classification.supercuspidalTemperedQuotientSingleBlock`
has exactly the type
`Langlands.Classification.SupercuspidalTemperedQuotientSingleBlockStatement.{uF, uV}`
of [the statement](SupercuspidalTemperedQuotientSingleBlockStatement.md). It
adds no hypotheses. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

The source result is the uniqueness half of the Langlands classification
(Kudla 1994, Theorem 2.2.2(b)). The proof does not use that theorem. It uses
the published second adjointness: a supercuspidal representation receives no
nonzero intertwiner from a properly induced admissible representation.

## Declarations

The module proves four lemmas and the target theorem.

1. `GeneralLinear.IsSupercuspidal.subsingleton_oppositeCoinvariants`. If `ρ`
   is supercuspidal and `B.parabolic F ≠ ⊤`, the coinvariants of `ρ` for the
   opposite unipotent radical `B.oppositeUnipotentSubgroup F` are a
   subsingleton. The opposite radical of `B` is the conjugate of the upper
   radical of the reversed shape `B.reverse` by `B.reverseMatrix F`
   (`B.reverse_unipotentSubgroup_map_conj`). The reversed parabolic is again
   proper (`B.reverse_parabolic_ne_top_iff`). The second clause of
   `IsSupercuspidal`, applied to `B.reverse` and the element
   `B.reverseMatrix F`, gives the vanishing.
2. `PadicField.TopologicalData.normalizedParabolicInduced_intertwiningMap_eq_zero_of_isSupercuspidal`.
   For `0 < n`, a proper block shape `B`, an admissible representation `σ`
   of the product Levi `B.Levi F.Carrier`, a supercuspidal `π` of
   `GL_n(F)`, and an intertwiner `f` from the normalized parabolic induction
   `T.normalizedParabolicInduced B σ.ρ` to `π`, we have `f = 0`. The first
   clause of the published theorem `Parabolic.normalizedSecondAdjointness`
   gives a linear equivalence `E` from these intertwiners to the intertwiners
   from `σ` to `CuspidalJacquetMultiplicity.oppositeJacquet T B π`. Its
   carrier is the opposite coinvariant space of lemma 1, which is a
   subsingleton. So `E f = 0`, and `f = 0` because `E` is injective.
   Admissibility of `π` is the first clause of `IsSupercuspidal`.
3. `TemperedLanglandsDatum.shape_length_eq_one_of_isSupercuspidal`. For
   `0 < n`, a tempered datum `d` of rank `n` and a supercuspidal `π` with
   `d.IsLanglandsQuotient π`, we have `d.shape.length = 1`. The proof has
   three steps.
   - The parabolic of `d.shape` is the whole group. Otherwise lemma 2
     applies to the surjection `q` from the standard module onto `π`. The
     standard module is by definition the normalized parabolic induction of
     the external tensor product of the twisted blocks
     `ν^(u_i) π_i`. Each twisted block is admissible
     (`RegularHeadExistence.twistedBlock_admissible_finiteLength`), so the
     tensor product is admissible (`FiniteTensor.isAdmissible_external`).
     Hence `q = 0`. But `π` is irreducible, so it is a simple module over
     the group algebra and therefore nontrivial. A nonzero vector of `π` has
     a preimage under `q`, which contradicts `q = 0`.
   - A block shape with the whole group as parabolic has at most one block
     index (`CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top`).
   - The shape has at least one block: with no blocks, the block sizes would
     sum to `0`, not to the positive rank `n`. So the length is `1`.
4. `TemperedLanglandsDatum.nonempty_standardModule_equiv_of_isSupercuspidal`.
   Under the hypotheses of lemma 3, the standard module is equivalent to `π`.
   The statement does not need this lemma. It is provided for users of the
   statement. By lemma 3 the shape has one block. The published
   `T.singleBlockNormalizedProductEquiv` identifies the one-block standard
   module with the twisted block `ν^(u_1) π_1`, reindexed to `GL_n(F)`. That
   block is irreducible (`RegularHeadExistence.twistedBlock_irreducible`,
   transported along the reindexing by
   `CuspidalSupport.isIrreducible_comp_mulEquiv_iff`), so the standard module
   is irreducible (`LengthTwo.isIrreducible_of_equiv`). The surjection `q` is
   nonzero, as in lemma 3. A nonzero intertwiner between irreducible
   representations is bijective (`Representation.IsIrreducible.bijective_or_eq_zero`),
   which gives the equivalence.

The target theorem applies lemma 3 at rank `n + 1`, with `Nat.succ_pos n`.
The field and block-carrier universes `uF` and `uV` remain independent, and
the arbitrary topological realization `T` is retained. In particular, `n = 0`
in the target covers `GL_1`; the positive-rank argument still applies.

## Comparison with the source route

Kudla's Theorem 2.2.2(b) and Henniart's §2.8 obtain the conclusion from the
uniqueness of Langlands data. Here the datum enters only through the
admissibility of its twisted blocks. The order of the exponents is not used.
Lemma 2 needs only admissible inducing data, so it says more: no nonzero
intertwiner goes from a representation induced from a proper block parabolic
with admissible inducing data to a supercuspidal representation.


## Source provenance and retained scope

The target is the derived consequence of the source classification described
in the unchanged statement Markdown. Its registered sources are:

| Registered source | Content SHA256 | Passage |
| --- | --- | --- |
| `kudla-1994-local-langlands-nonarchimedean` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | Theorem 2.2.2(a)–(b), printed pp. 373–374, PDF pp. 383–384 of the volume |
| `henniart-2002-characterization` | `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306` | §2.8, printed p. 596 (PDF p. 10), and §3.2–3.3, printed pp. 597–598 (PDF pp. 11–12) |

These passages give the provenance and intended application of the proposition.
The implemented proof instead uses the already published second-adjointness
proof and the actual Jacquet vanishing built into the supercuspidal predicate.
It does not construct Langlands data, prove the full classification or prove
Henniart's Theorem 1.6(b). The optional fourth lemma supplies an actual
representation equivalence after the one-block conclusion, with the same
hypotheses as the third lemma.
