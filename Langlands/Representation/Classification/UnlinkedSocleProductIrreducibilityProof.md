# Products of Zelevinsky socles with mutually unlinked multisegments

Author: Worker 4879.

This module proves the published proposition
`Langlands.Classification.UnlinkedSocleProductIrreducibility` of
[TadicBlockReductionStatement](TadicBlockReductionStatement.md), which states Zelevinsky
(1980), Proposition 8.5 (printed p.196, PDF p.33). The theorem is
`Langlands.Classification.unlinkedSocleProductIrreducibility`. Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`, and its type is
exactly `UnlinkedSocleProductIrreducibility.{uF, uV} F T`, with independent field and
carrier universes. The statement is unchanged and no hypothesis is added.

The statement says: for every `n`, every block shape `B : BlockShape n`, multisegments
`a i` and smooth representations `π i` of `GL_{B.size i}` with
`(a i).IsZelevinskySocle (π i)`, if for `i ≠ j` no segment of `a i` is linked with a
segment of `a j`, then the normalized product `X = (T.normalizedProductInductionFunctor B).obj π`
satisfies `(∑ i, a i).IsZelevinskySocle X`. This includes `n = 0` and an empty outer
product.

## Route

The proof follows Zelevinsky's proof of Proposition 8.5 without the reduction to two
factors: `X` embeds in a precedence-ordered standard product whose irreducible socle is
`⟨∑ a_i⟩`; dually every irreducible quotient of `X` is `⟨∑ a_i⟩`; this representation
occurs at most once in `X` (Zelevinsky's 8.4, here obtained from the Library's form of
Theorem 7.1); hence `X` is irreducible. Irreducibility of `X` together with the embedding
gives the conclusion. The proof uses only published Library results and
the following auxiliary results of this module, all in the namespace
`Langlands.Classification.UnlinkedSocleProduct`.

### An irreducibility criterion

`hasJordanHolderMultiplicity_one`: an irreducible smooth representation `P` with an
equivalence `P ≃ τ` has Jordan–Hölder multiplicity `1` with respect to `τ`. Its proof takes the
published witness `compositionMultiplicity_witness` of the chosen series of `P`, evaluates
the count by `IrreducibleOperator.compositionMultiplicity_self`, and transports along the
equivalence with `equivJordanHolderMultiplicityTransport`.

`isIrreducible_of_multiplicity_le_one`: let `A` be a nonzero finite-length smooth
representation (for any group `G` with a topology) and `τ` a smooth representation such
that `A` has Jordan–Hölder multiplicity `m ≤ 1` with respect to `τ`, every irreducible
subrepresentation of `A` (an irreducible `P` with an injective morphism `P ⟶ A`) is
equivalent to `τ`, and every irreducible quotient of `A` (an irreducible `Q` with a
surjective morphism `A ⟶ Q`) is equivalent to `τ`. Then `A` is irreducible.

Proof: `A` has an irreducible subrepresentation `j : P ⟶ A`
(`SegmentHeadSupport.exists_irreducible_subrepresentation`). If `j` is surjective it is
bijective, and `A` is irreducible by isomorphism invariance. Otherwise the quotient
`C = A / range j` is nonzero and of finite length, so it has an irreducible quotient
`r : C ⟶ Q` (`SegmentHeadSupport.exists_irreducible_quotient`). By hypothesis `P ≃ τ` and
`Q ≃ τ` (the latter for the surjection `A ⟶ C ⟶ Q`). The short exact sequence
`0 → P → A → C → 0` splits the multiplicity `m = m_P + m_C`
(`jordanHolderShortExactDecomposition`), `m_P = 1` by the previous lemma, and `m_C ≥ 1` by
monotonicity along the surjection `C ⟶ Q` (`jordanHolderSurjectiveMonotonicity`) and
multiplicity one of `Q`. So `m ≥ 2`, contradicting `m ≤ 1`.

### Multiplicity one (Zelevinsky 7.1 and 8.4)

`compositionMultiplicity_le_one`: for a datum `D` of segment socles
(`D.HasSegmentSocles`) and `S` with `D.IsZelevinskySubrepresentation S`, the chosen
composition multiplicity of `S` in the finite-length product `D.induced` is at most `1`.

Proof: work in the published graded Grothendieck ring `Aubert.gradedInductionRing`, built
from `Aubert.binaryProductExactness` and `Aubert.gradedInductionRingLaws`, and fix a
nontrivial unitary additive character `ψ` (`padicUnitaryAdditiveCharacterExists`). The
isomorphism class of `S` is a label of `D.multisegment` in the sense of
`Aubert.SegmentPolynomialSurjectivity.IsLabel` (witnessed by `S` and `D` itself), so its
label weight is `1` (`labelWeight_of_isLabel`). Since `ζ(D.multisegment)` is effective
(`isEffective_zeta`), `coeff_mul_le_weightedCount` bounds the coefficient of this label in
`ζ(D.multisegment)` by the weighted label count, which is at most `1` by
`labelCount_zeta_le_one` (the Library's weak-label form of Zelevinsky's Theorem 7.1,
applied with the published `highestDerivativeLabelStep`). By `zeta_multisegment`,
`ζ(D.multisegment)` is the class of `D.induced`, and by
`coeff_gradedInclusion_ofRepresentation` that coefficient is the composition multiplicity
of `S` in `D.induced`.

### Irreducible quotients via smooth duals (Zelevinsky 7.10)

`isLinked_of_dual`: if the dual segments `Δ^∨` and `Γ^∨` are linked, then `Δ` and `Γ` are
linked. One of `Δ^∨, Γ^∨` precedes the other; by `Segment.precedes_dual_iff` the
original segments precede in the opposite order, and precedence implies linkage.

`isZelevinskySocle_of_quotient`: for `0 < n` and data `B, a, π` as in the statement,
every irreducible quotient `q : X ⟶ Q` (`q` surjective) satisfies
`(∑ i, a i).IsZelevinskySocle Q`.

Proof:

1. Each `π i` is irreducible, hence admissible
   (`TwoFactorCommutativity.isAdmissible_of_isIrreducible`), and so is `Q`; the smooth dual
   `Q^∨` is irreducible (`SmoothRep.isIrreducible_contragredient_iff`, with the published
   cofinality of compact open subgroups of `GL_n`).
2. By `Multisegment.IsZelevinskySocle.contragredient` (the Library's form of Zelevinsky
   7.10 for socles), `(π i)^∨` is a Zelevinsky socle of the dual multisegment
   `(a i).map Segment.dual`. Choose data `d' i` realizing this and let
   `D' = SegmentProductDatum.concatenate B d'`.
3. `D'` is precedence-ordered by `concatenate_isPrecedenceOrdered`: each `d' i` is
   ordered, and segments in different blocks are unlinked, because dual segments of
   `a i` and `a j` (`i ≠ j`) that were linked would make the original segments linked
   (`isLinked_of_dual`). `D'` has segment socles (`concatenate_hasSegmentSocles`), so
   `orderedMultisegmentSocleExistence` (Zelevinsky 6.1(a)) gives a Zelevinsky socle `S'` of `D'`.
4. The composite of the dual of `q` (injective, `contragredientMap_injective_of_surjective`),
   the inverse of the published product-dual equivalence
   `TwoFactorCommutativity.productSmoothDual` (`∏ (π i)^∨ ≃ X^∨`), and the published
   embedding `socleProductEmbedding` (`∏ (π i)^∨ ↪ D'.induced`) is an injective
   intertwiner `Q^∨ ↪ D'.induced`. By `IsIrreducibleSocle.of_subrepresentation`, `Q^∨`
   is the irreducible socle of `D'.induced`.
5. Since `D'.multisegment = ∑ i, (a i).map Segment.dual = (∑ i, a i).map Segment.dual`
   (`concatenate_multisegment` and additivity of `Multiset.map`), `Q^∨` is a Zelevinsky
   socle of `(∑ i, a i).map Segment.dual`. Applying `contragredient` once more and using
   `Segment.dual_dual`, `Q^∨∨` is a Zelevinsky socle of `∑ i, a i`, and so is `Q` through
   the published bidual isomorphism `SmoothRep.bidualIso` of the admissible `Q`.

### The main theorem

Given `n, B, a, π` and the hypotheses, choose data `d i` with `(d i).multisegment = a i`
and `(d i).IsZelevinskySocle (π i)`, and let `D = SegmentProductDatum.concatenate B d`.

- `D.multisegment = ∑ i, a i` (`concatenate_multisegment`); `D` is precedence-ordered by
  `concatenate_isPrecedenceOrdered` and the nonlinkage hypothesis; `D` has segment socles.
- `orderedMultisegmentSocleExistence` gives a Zelevinsky socle `S` of `D`, and
  `socleProductEmbedding` gives an injective intertwiner `j : X ↪ D.induced`.
- It suffices to prove that `X` is irreducible: then `IsIrreducibleSocle.of_subrepresentation`
  applied to `j` shows that `X` is the irreducible socle of `D.induced`, which with the facts
  on `D` is `(∑ i, a i).IsZelevinskySocle X`.

Irreducibility of `X`:

- If `n = 0`, `X` is irreducible by the published `rankZeroNormalizedProduct_isIrreducible`.
- If `n > 0`, apply `isIrreducible_of_multiplicity_le_one` with `A = X`, `τ = S` and `m` the
  chosen composition multiplicity of `S` in `X`.
  `X` is nonzero (`RegularHeadExistence.nontrivial_normalizedProductInduction`, as each
  `π i` is irreducible, hence nonzero) and has finite length as a subrepresentation of the
  finite-length `D.induced` (`Aubert.SegmentProductClass.hasFiniteLength_induced`).
  - `m ≤ 1`: by monotonicity along the injection `j`
    (`jordanHolderInjectiveMonotonicity`), `m` is at most the multiplicity of `S` in
    `D.induced`, which is at most `1` by `compositionMultiplicity_le_one`.
  - An irreducible subrepresentation `P ↪ X` gives `P ↪ D.induced`, so `P ≃ S` because the
    socle of `D.induced` is unique up to equivalence
    (`IsIrreducibleSocle.nonempty_equiv_of_subrepresentation`).
  - An irreducible quotient `X ↠ Q` is a Zelevinsky socle of `∑ i, a i`
    (`isZelevinskySocle_of_quotient`), as is `S` (through `D`), so `Q ≅ S` by
    `nonempty_iso_of_isZelevinskySocle`.

## Relation to the source

Zelevinsky reduces to `p = 2`, uses `π(a_1) × π(a_2) = π(a_1 + a_2)` for a suitable
ordering (his 6.5), the unique irreducible submodule `⟨a⟩` of `π(a)` (6.1(a)), duality
(7.10) to obtain the unique irreducible quotient, and the multiplicity-one statement 8.4.
The Lean proof treats all `p` factors at once through the concatenated datum `D`
(the published `UnlinkedSocleProductEmbedding` module), and obtains 8.4 for the needed
case from the Library's form of Theorem 7.1 (`labelCount_zeta_le_one`) rather than from
Zelevinsky's derivative argument for 8.4. The final step "either irreducible or
multiplicity at least 2" is the criterion `isIrreducible_of_multiplicity_le_one`.

Source: `zelevinsky-1980-induced-ii`, A. V. Zelevinsky, Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n), Ann. Sci. ENS (4) 13
(1980), 165–210; Proposition 8.5 and its proof, printed p.196 (PDF p.33).
