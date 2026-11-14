# Reductions of the canonical Sharp targets of Corollaire 3.9

Module `Langlands.Representation.Aubert.General.CanonicalRationalSharpReductionStatements`.
Authors: Worker 29, with Worker 3640, who chose this block (block (iv)) for
the general Aubert program (Task 3640) and fixed its five input sets.

The module declares five Prop-valued definitions in
`Langlands.Aubert.General.RationalPointFamily`, each with universe parameters
`u` and `v`. The review entry is
`CanonicalRationalSharpSupportRetentionReductionStatement`. Each definition is
a curried implication between whole published propositions. None is proved
here. None proves its conclusion or discharges an input, and none adds a
premise to its conclusion: each conclusion is the unchanged canonical Sharp
target of `CanonicalRationalComplexTargets`, and each input is the unchanged
published proposition.

Throughout, `E#` is the cokernel of the actual canonical complex at
removed-root degree `|S| - |I|`, as in `CanonicalRationalComplexTargets.md`.

## The inputs

- `CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`
  (`RationalWholeCuspidalDecompositionStatement`), written *Whole* below. It is
  the two-factor decomposition of the whole smooth category in Renard,
  Théorème VI.3.5, printed p. 146 / PDF p. 152: every smooth representation is
  the coproduct of one part all of whose subquotients are cuspidal and one
  part none of whose nonzero subquotients is cuspidal. Its universe
  parameters are the field universe and the carrier universe. Here it is
  always taken at `.{u, max (u + 1) v}`.
- `RationalCorrectedGradedVanishingStatement.{u, v}`
  (`RationalCorrectedFiltrationTargets`), written *GradedVanishing* below. For
  `E` in the actual support category of `L_I`, a nonzero graded piece of the
  support filtration of `r_I(E_J)` at a Weyl element `w` forces
  `w L_I w⁻¹ = L_K` for a standard `K ⊆ J` (erratum, pp. 4688–4689, with the
  Ban–Jantzen double-coset correction, as recorded in that module's
  Markdown).
- `DynamicInductionFiniteLengthStatement` and
  `DynamicJacquetFiniteLengthStatement` (`PrerequisiteStatements`), written
  *DynInd* and *DynJac* below. Actual normalized parabolic induction and
  Jacquet restriction along the dynamic parabolic of every cocharacter of
  every connected reductive group over every nonarchimedean local field
  preserve finite length: Renard VI.6.2, printed p. 178 / PDF p. 184, and
  VI.6.4, printed p. 179 / PDF p. 185. Both are always taken at
  `.{u, max (u + 1) v}`.
- `RationalInducedK0WeylConjugacyStatement.{u, v}`
  (`RationalInducedWeylConjugacyTarget`), written *Weyl* below. For every
  actual normalizer element `n` of the rational torus points with
  `x ∈ L_J ↔ n⁻¹ x n ∈ L_I`, `i_J ∘ Ad(n) = i_I` as integer-linear maps of
  exact finite-length Grothendieck groups. This is Aubert (1995),
  identity (1.2), printed p. 2181 / PDF p. 3. The proposition keeps its own
  finite-length premises `hiFl`, `hrFl` inside its binders, as published.

In each input, `.{u, max (u + 1) v}` means field universe `u` and carrier
universe `max (u + 1) v`. This is the carrier universe of every conclusion at
`u, v`, so no universe is lowered or raised.

These are items 1 (*Whole*), 4 (*GradedVanishing*), 6 (*DynInd*, *DynJac*)
and 3 (*Weyl*) of the bottleneck list in
`notes/aubert/general-program-dependency-matrix.md`. Induced K0 Weyl
conjugacy is kept as an explicit input. The Sharp class formula,
induction compatibility and involutivity of `D_G` are not inputs: the checked
proofs derive them, as described under *Provenance and intended proofs*.

## `CanonicalRationalSharpSupportRetentionReductionStatement`

```
CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
  CanonicalRationalSharpSupportRetentionStatement.{u, v}
```

The conclusion is `CanonicalRationalSharpSupportRetentionStatement`: for
every standard `I` and every smooth `E` in the actual support category
`Alg({I})`, `E#` lies in `Alg({I})`. This retention of the support type is
derived, not a numbered claim of the sources. It is what iterating `#` on
`Alg({I})` needs: the erratum, printed p. 4687 / PDF p. 1, defines `Alg({I})`
and `E#` is formed on it in Remarques (1), printed p. 4690 / PDF p. 4. *Whole*
is the only input.

## `CanonicalRationalSharpFiniteLengthReductionStatement`

```
DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
  DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
    CanonicalRationalSharpFiniteLengthStatement.{u, v}
```

The conclusion is `CanonicalRationalSharpFiniteLengthStatement`: for every
standard `I` and every finite-length smooth `E`, `E#` has finite length. This
is the finite-length obligation that Aubert (1995), Corollaire 3.9 (a),
printed p. 2189 / PDF p. 11, needs before the class `[E#]` makes sense. It is
stated for every finite-length `E`, not only for members of `Alg({I})`.
*DynInd* and *DynJac* are the only inputs.

## `CanonicalRationalSharpIrreducibleReductionStatement`

```
CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
  RationalCorrectedGradedVanishingStatement.{u, v} →
    DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
      DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
        RationalInducedK0WeylConjugacyStatement.{u, v} →
          CanonicalRationalSharpIrreducibleStatement.{u, v}
```

The conclusion is `CanonicalRationalSharpIrreducibleStatement`: for every
standard `I` and every `E` in the cuspidal series `𝔈(I)` (Aubert's
Notation 1.6, whose members are irreducible), `E#` is irreducible, and in
particular nonzero. This is Aubert (1995), Corollaire 3.9 (b), printed
p. 2189 / PDF p. 11. Aubert's proof uses (a) together with Théorème 1.7 (2)
and (4); the proof of 1.7 (2), printed p. 2182 / PDF p. 4, uses identity
(1.2).

## `CanonicalRationalSharpCuspidalSeriesReductionStatement`

```
CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
  RationalCorrectedGradedVanishingStatement.{u, v} →
    DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
      DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
        RationalInducedK0WeylConjugacyStatement.{u, v} →
          CanonicalRationalSharpCuspidalSeriesStatement.{u, v}
```

The conclusion is `CanonicalRationalSharpCuspidalSeriesStatement`: for every
standard `I` and every `E ∈ 𝔈(I)`, there are a standard `I'` and an actual
point `n`, related to `I` by the canonical `rootAssociation`, with
`L_{I'} = n L_I n⁻¹` and `E# ∈ 𝔈(I')`. This retention of the cuspidal series
is derived. It is used in Aubert's proof of Corollaire 3.9 (c), printed
p. 2189 / PDF p. 11, which applies (a) and (b) to `E#`. The inputs are the
same five as for the irreducibility reduction.

## `CanonicalRationalSharpInvolutionReductionStatement`

```
CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
  RationalCorrectedGradedVanishingStatement.{u, v} →
    DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
      DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
        RationalInducedK0WeylConjugacyStatement.{u, v} →
          CanonicalRationalSharpInvolutionStatement.{u, v}
```

The conclusion is `CanonicalRationalSharpInvolutionStatement`: for every
standard `I` and every `E ∈ 𝔈(I)`, there is an isomorphism of smooth
representations `(E#)# ≅ E`, with both cokernels taken at the same degree
`|S| - |I|`. It is an actual isomorphism in `SmoothRep`, not an equality of
Grothendieck classes. This is Aubert (1995), Corollaire 3.9 (c), printed
p. 2189 / PDF p. 11, which Aubert derives from the involutivity of `D_G`
(Théorème 1.7 (3)). The inputs are the same five as for the irreducibility
reduction.

## Scope

All inputs and conclusions are the published propositions themselves,
quantified over the same actual setting:

- every nonarchimedean local field, including positive characteristic;
- every connected reductive group, with its actual maximal split torus,
  generic cocharacter and actual simple relative roots, including the empty
  set;
- the canonical `pointTopology` on rational points in the conclusions,
  GradedVanishing and *Weyl*, and `rationalPointTopology` in *Whole*, *DynInd*
  and *DynJac*, as published;
- field universe `u` and representation carriers in `max (u + 1) v`, with
  `u` and `v` independent.

No proposition restricts to split, quasisplit or characteristic-zero groups,
or to `GL`. The canonical class formula is not here: its reduction is the
published `CanonicalRationalSharpClassFormulaReductionStatement` of
`CanonicalRationalComplexReductionStatements`.

## Provenance and intended proofs

These are derived, internal statements. They make no new claim from the
literature. Their mathematical content is that of the cited sources through
the published targets, whose own Markdown records the source correspondence.
Aubert's Proposition 3.2 is not used.

Each implication has been checked in Lean, against the current Library and
the pending drafts named below, with standard axioms only. No input beyond
those listed was needed. The proofs belong to separate `lean.proof@1`
successor tasks. Statement review does not establish them. The checked
routes are as follows.

- Support retention. From *Whole*, the published theorems
  `rationalCuspidalExtractionInputs_of_wholeStatement` and
  `rationalCuspidalJacquetFactorExtraction_of_inputs` give cuspidal
  Jacquet-factor extraction, and
  `rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction`
  gives support association. With
  `rationalSupportCategoryDecomposition_of_wholeStatement` and
  `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement`,
  `rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`
  gives induction-Jacquet stability of the support category. The published
  `rationalSharpSupportRetention_of_inductionJacquet` gives the rational
  target.
- Finite length. The reduction `rationalSharpFiniteLengthReduction` of
  `RationalSharpFiniteLengthReductionStatement` takes *DynInd* and *DynJac*
  and gives the rational target. That statement is in the block (ii) module
  `RationalDetectionFiniteLengthReductionStatements`, candidate
  `69993db0-c020-4fc3-b0eb-b213a9eea777`, accepted in review and not yet in
  the Library. Its proof goes to its own successor task.
- Class formula, derived. As for the published
  `CanonicalRationalSharpClassFormulaReductionStatement`: from *Whole*, the
  steps above give extraction, association and induction-Jacquet stability.
  The block (ii) reductions give zero detection from extraction, then
  exactness detection. The published
  `rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association`
  gives support-category Jacquet vanishing from quotient compactness
  (`dynamicParabolicQuotientCompact`) and association. Then
  `rationalSharpClassFormulaReduction` (Task 6483,
  `18c36a7c-1b08-4443-b90a-38a4f0b9532a`, shared draft) takes GradedVanishing,
  induction-Jacquet stability, exactness detection and Jacquet vanishing and
  gives `RationalSharpClassFormulaStatement`.
- Induction compatibility and involutivity, derived. The published
  `rationalInductionCompatibility_of_expansion_and_inducedWeyl` takes the
  published `rationalGeometricK0Expansion` and *Weyl*. The published
  `rationalInvolutivityStatement_of_inducedK0WeylConjugacy` takes *Weyl*
  alone.
- Irreducibility. The published `rationalSharpIrreducibleStatement_of_inputs`
  takes *DynInd*, *DynJac*, induction compatibility, involutivity and the
  class formula.
- Cuspidal series. The reduction `rationalSharpCuspidalSeriesReduction`
  (Task 6484, `b5652c2b-8c8a-41a5-9af8-09a7f7a8412c`, shared draft) takes
  rational support retention and irreducibility.
- Involution. The published `rationalSharpInvolutionStatement_of_inputs` takes
  *DynInd*, *DynJac*, involutivity, the class formula and cuspidal-series
  retention.

In each case the canonical form comes from the bridge
`canonicalRationalSharp…_of_rational` of Task 6425
(`d7477c1e-06c2-43ec-9035-3eb6b594058b`, shared draft). So the
support-retention proof depends on Task 6425 only; the finite-length proof
also on the block (ii) finite-length reduction; and the irreducibility,
cuspidal-series and involution proofs on Task 6425, the block (ii) zero- and
exactness-detection reductions and Task 6483, the last two also on Task 6484.
