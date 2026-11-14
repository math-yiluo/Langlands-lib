# Reductions of canonical corrected Theorem 3.6, the associated-Levi comparison and the Sharp class formula

Module `Langlands.Representation.Aubert.General.CanonicalRationalComplexReductionStatements`.
Authors: Worker 29, with Worker 3640, who chose this block (block (iii)) for
the general Aubert program (Task 3640) and fixed its three input sets.

The module declares three Prop-valued definitions in
`Langlands.Aubert.General.RationalPointFamily`, each with universe parameters
`u` and `v`. The review entry is
`CanonicalRationalCorrectedTheorem36ReductionStatement`. Each definition is an
implication between whole published propositions. None is proved here. None
proves its conclusion or discharges an input, and none adds a premise to its
conclusion: each conclusion is the unchanged canonical target of
`CanonicalRationalComplexTargets`, and each input is the unchanged published
proposition.

## The two inputs

- `CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`
  (`RationalWholeCuspidalDecompositionStatement`), written *Whole* below. It is
  the two-factor decomposition of the whole smooth category in Renard,
  Théorème VI.3.5, printed p. 146 / PDF p. 152: every smooth representation is
  the coproduct of one part all of whose subquotients are cuspidal and one
  part none of whose nonzero subquotients is cuspidal. It has two universe
  parameters, the field universe and the carrier universe. Here it is always
  taken at `.{u, max (u + 1) v}`, that is, at field universe `u` and at
  carrier universe `max (u + 1) v`. This is the carrier universe of every
  conclusion at `u, v`, so no universe is lowered or raised.
- `RationalCorrectedGradedVanishingStatement.{u, v}`
  (`RationalCorrectedFiltrationTargets`), written *GradedVanishing* below. For
  `E` in the actual support category of `L_I`, a nonzero graded piece of the
  support filtration of `r_I(E_J)` at a Weyl element `w` forces
  `w L_I w⁻¹ = L_K` for a standard `K ⊆ J` (erratum, pp. 4688–4689, with the
  Ban–Jantzen double-coset correction, as recorded in that module's
  Markdown).

These are items 1 and 4 of the bottleneck list in
`notes/aubert/general-program-dependency-matrix.md`. No dynamic
finite-length input appears as an antecedent. Where the class formula needs
finite-length preservation to build `D_G`, its conclusion already quantifies
over every proof of it, as published.

## `CanonicalRationalCorrectedTheorem36ReductionStatement`

```
CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
  RationalCorrectedGradedVanishingStatement.{u, v} →
    CanonicalRationalCorrectedTheorem36Statement.{u, v}
```

The conclusion is `CanonicalRationalCorrectedTheorem36Statement`. For every
nonarchimedean local field, connected reductive group, maximal split torus,
generic cocharacter, linear order on the actual simple relative roots and
standard `I`, every smooth representation in the actual support category
`Alg({I})` of `L_I` has a normalized standard complex that is exact before its
retained terminal term. This is the corrected Théorème 3.6: Aubert (1995),
printed p. 2187 / PDF p. 9, with the proof replaced in the 1996 erratum,
printed p. 4687 / PDF p. 1, sequence (∗), for all `E` in `Alg({I})` with no
finite-length restriction.

## `CanonicalRationalAssociatedLeviComparisonReductionStatement`

```
RationalCorrectedGradedVanishingStatement.{u, v} →
  CanonicalRationalAssociatedLeviComparisonStatement.{u, v}
```

The conclusion is `CanonicalRationalAssociatedLeviComparisonStatement`, the
associated-Levi Jacquet comparison of display (∗∗) of the erratum, printed
p. 4690 / PDF p. 4, on the actual normalizer/full-centralizer quotient, for
the canonical Coxeter system and every lift of its longest representatives.
*Whole* is not an input: GradedVanishing is the only open input of this
comparison.

## `CanonicalRationalSharpClassFormulaReductionStatement`

```
CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
  RationalCorrectedGradedVanishingStatement.{u, v} →
    CanonicalRationalSharpClassFormulaStatement.{u, v}
```

The conclusion is `CanonicalRationalSharpClassFormulaStatement`: for every
finite-length member `E` of the actual support category,
`D_G([E]) = (-1)^{|I|} [E#]` in the finite-length Grothendieck group, where
`E#` is the actual terminal cokernel. As in the published
`SharpClassFormulaTarget`, finite length of `E#` is a premise of the formula;
it is not concluded here (that is the separate Sharp finite-length target). This
is Aubert (1995), Corollaire 3.9 (a), printed p. 2189 / PDF p. 11, which is
stated for `E` in `𝔅(I)`; the erratum, p. 4690, Remarque (1), uses it for
`E` in `Alg({I})`. As in the published target, the formula is asserted for
every proof of the finite-length preservation used to build `D_G`.

## Scope

All inputs and conclusions are the published propositions themselves,
quantified over the same actual setting:

- every nonarchimedean local field, including positive characteristic;
- every connected reductive group, with its actual maximal split torus,
  generic cocharacter and actual simple relative roots, including the empty
  set;
- the canonical `pointTopology` on rational points in the conclusions and
  GradedVanishing, and `rationalPointTopology` in *Whole*, as published;
- field universe `u` and representation carriers in `max (u + 1) v`, with
  `u` and `v` independent.

No proposition restricts to split, quasisplit or characteristic-zero groups,
or to `GL`. The fixed-Levi comparison is not here: its rational target is
already proved (`rationalFixedLeviComparison`), so its canonical form needs
only the bridge of Task 6425.

## Provenance and intended proofs

These are derived, internal statements. They make no new claim from the
literature. Their mathematical content is that of the cited sources through
the published targets, whose own Markdown records the source correspondence.
Aubert's Proposition 3.2 is not used.

Each implication has been checked in Lean, against the current Library and
the pending drafts named below, with standard axioms only. The proofs belong
to separate `lean.proof@1` successor tasks. Statement review does not
establish them. The checked routes are as follows.

- From *Whole*, the published theorems
  `rationalCuspidalExtractionInputs_of_wholeStatement` and
  `rationalCuspidalJacquetFactorExtraction_of_inputs` give cuspidal
  Jacquet-factor extraction. Then
  `rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction` gives
  support association. Together with
  `rationalSupportCategoryDecomposition_of_wholeStatement` and
  `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement`,
  `rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`
  gives induction-Jacquet stability of the support category. So extraction
  is derived from the splitting and is not an added input.
- Exactness detection follows from extraction by the two reductions of the
  block (ii) statement module `RationalDetectionFiniteLengthReductionStatements`
  (zero detection from extraction, then exactness from zero detection). That
  module is candidate `69993db0-c020-4fc3-b0eb-b213a9eea777`, accepted in
  review and not yet in the Library. Its proofs go to their own successor
  tasks.
- Theorem 3.6. The published `rationalCorrectedTheorem36_of_inputs` takes the
  rational Bruhat decomposition (`rationalBruhat`), GradedVanishing, the
  graded transition (`rationalCorrectedGradedTransitionStatement`, proved),
  induction-Jacquet stability and exactness detection. It gives the rational
  target, and `canonicalRationalCorrectedTheorem36_of_rational` (Task 6425,
  `d7477c1e-06c2-43ec-9035-3eb6b594058b`, shared draft) gives the canonical
  form.
- Associated-Levi comparison. The published
  `rationalAssociatedLeviComparisonStatement_of_published` takes the rational
  Bruhat decomposition, dynamic quotient compactness, surviving support, the
  orbit radical and modulus statements (all proved), GradedVanishing and the
  graded transition. `canonicalRationalAssociatedLeviComparison_of_rational`
  (Task 6425) gives the canonical form.
- Class formula. The reduction `rationalSharpClassFormulaReduction` of
  `RationalSharpClassFormulaReductionStatement` (Task 6483,
  `18c36a7c-1b08-4443-b90a-38a4f0b9532a`, shared draft) takes GradedVanishing,
  induction-Jacquet stability, exactness detection and support-category
  Jacquet vanishing. The published
  `rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association`
  derives Jacquet vanishing from quotient compactness
  (`dynamicParabolicQuotientCompact`) and support association.
  `canonicalRationalSharpClassFormula_of_rational` (Task 6425) gives the
  canonical form.

So the Theorem 3.6 and class-formula proofs depend on Task 6425 and the block
(ii) reductions, the class-formula proof also on Task 6483, and the
associated-Levi proof on Task 6425 only.
