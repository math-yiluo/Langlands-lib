# Rational support-category exactness detection from zero detection

Module `Langlands.Representation.Aubert.General.RationalSupportCategoryExactnessReduction`.

Authors:

* Worker 128 wrote the rational specialization
  `rationalSupportCategoryExactnessDetection_of_zeroDetection` in the shared
  draft of Task 4194 (`d70a1edd-5a84-4b03-aecf-2818901809d4`). Worker 4194
  checked it. It is reused unchanged from revision 2 of that draft, with its
  description below.
* Worker 499 wrote the published generic exactness reduction. Worker 379's
  support-category definitions, targets and subquotient closure are reused.
  Worker 480's published unipotent-regularity adapter, with Worker 64's
  import-compatibility correction, supplies compact containment.
* Worker 29, with coauthor Worker 3640 (Task 3640): the statement import and
  the final theorem `rationalSupportCategoryExactnessDetectionReduction`.
  Worker 29 rechecked the module against Library
  `c0debd6f4dd02fdd68d70811cf610906b945a962` together with the statement
  module
  [`RationalDetectionFiniteLengthReductionStatements`](RationalDetectionFiniteLengthReductionStatements.md).

* Worker 275 verified the rational specialization against the published generic
  reduction and prepared this proof pair for Task 6583
  (`e9fddf52-5367-4151-a290-413d98622e89`).

**Scope.** This is an internal conditional reduction between two published
propositions. The module proves the published reduction proposition
`RationalSupportCategoryExactnessDetectionReductionStatement.{u, v}`, the
implication `RationalSupportCategoryZeroDetectionStatement.{u, v} →
RationalSupportCategoryExactnessDetectionStatement.{u, v}`. It proves neither
the premise nor `RationalSupportCategoryExactnessDetectionStatement.{u, v}`
unconditionally. The unconditional exactness theorem is owned by Task 4194;
it waits on a published proof of rational zero detection, owned by Task 4193
(`db02aabd-9901-4fae-9583-ec28c66aec3c`).

Remark, not formalized here: the premise cannot simply be dropped, because
exactness detection implies zero detection. Take `f : 0 ⟶ E` and `g : E ⟶ 0`.
The pair is exact exactly when `E` is zero, and every Jacquet pair is exact
exactly when the Jacquet module of `E` is zero. So a proof of the exactness
target needs a proof of rational zero detection.

## Declarations

The namespace is `Langlands.Aubert.General.RationalPointFamily`.

`rationalSupportCategoryExactnessDetection_of_zeroDetection` has premise
`RationalSupportCategoryZeroDetectionStatement.{u, v}` and conclusion
`RationalSupportCategoryExactnessDetectionStatement.{u, v}`. The universes `u`
and `v` are independent. There are no other parameters.

`rationalSupportCategoryExactnessDetectionReduction` proves
`RationalSupportCategoryExactnessDetectionReductionStatement.{u, v}`. Its
proof is the term
`fun hdet => rationalSupportCategoryExactnessDetection_of_zeroDetection hdet`;
the input and the conclusion keep their universes, and no premise is added.

## Proof of the conditional theorem

The proof introduces all the data displayed by the exactness target. It
installs the instances that the target installs:

- the affine-morphism instance from `hG`;
- the monomorphism instance from `hi`;
- the evaluation topology `pointTopology` on `RationalPoint k G.X`;
- the finite enumeration of the actual simple roots,
  `GroupScheme.simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν`.

No family, topology, representation category or association relation is
replaced.

It then applies the published generic theorem
`ExactnessDetection.supportCategoryExactnessDetection_of_zeroDetection`. That
theorem takes two inputs.

1. **Compact limits.** For each finite set `J` of simple roots,
   `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
   shows that `unipotent i ν J` is a limit of compact subgroups. It uses only
   the displayed `i`, `ν`, `hStandard`, `hG`, `hi` and `hν`.
2. **Zero detection.** This is the premise `hdet`, applied to the same field,
   group, torus, cocharacter, structural hypotheses, closedness proofs `hU`,
   `hM` and comparisons `hN`, `hZ`.

The zero-detection and exactness targets have the same rational premises.
They pass the same arguments to the generic families: the standard
`parabolic`, `levi` and `unipotent` families, the semidirect decompositions
`isSemidirectDecomposition_of_standardCocharacterStatement` and
`isSemidirectDecomposition_in_levi`, and `rootAssociation i ν hN hZ`. Both
quantify over detecting pairs `J, n` satisfying both the root association and
the displayed Levi-conjugation equivalence. Representation carriers are in
`Type (max (u + 1) v)`. Only the middle representation must lie in the
support category. The two outer representations are arbitrary smooth
modules.

### The generic reduction

The generic reduction is described in detail in
`SupportCategoryExactnessReduction.md`.

- **Forward direction.** Full short exactness of each Jacquet functor implies
  that it preserves every exact pair. The pair need not be a short exact
  sequence.
- **Converse.** The image of `f` is a subrepresentation of the supported
  object, so it is supported. Zero detection on it gives `f ≫ g = 0`. The map
  `g` then descends to the cokernel of `f`, which is a supported quotient.
  Injectivity of the descended map is detected by the Jacquet functors, and
  it gives exactness.

## Dependencies

Compact limits come from this chain of published declarations.

- `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
  in `Langlands.Representation.Aubert.General.RationalUnipotentRegularity`.
  It applies `hStandard` to `rootSet i ν J`, which gives a standard
  cocharacter and an equality of the standard and dynamic unipotent subgroup
  functors. Evaluating at the identity test object gives an equality of the
  actual point subgroups.
- `BruhatTits.dynamicUnipotentCompactOpenContainment` in
  `Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof`. It provides
  compact open subgroups containing given compact sets.
- `BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups` in
  `Langlands.BruhatTits.Unipotent.JacquetCompactContainmentProof`. It turns
  this into the compact-limit predicate, which forgets openness.

The dynamic proof holds for every nonarchimedean local field and every
connected reductive group in its statement. It adds no premise on the
characteristic, splitting, quasi-splitting, rank, endpoints or compact
limits.

The generic reduction relies on these published declarations.

- `jacquetFunctor_map_isShortExact` in
  `Langlands.Representation.Aubert.General.AlternatingOperator`. It applies
  `Jacquet.Localization.characterLocalizationExactness` to the trivial
  character, and gives full exactness on arbitrary smooth modules.
  Normalization changes the action but not the underlying maps. No
  finite-length, admissibility or finite-generation statement is used.
- `IsInSupportCategory.of_isSubquotient`, for support closure. It is proved
  from `Langlands.smoothSubquotientTransitivity`.

The subobject and quotient witnesses and the image, kernel and quotient
constructions are listed in the generic reduction's Markdown.

None of these declarations uses the Langlands classification, independence
of characters, a geometric lemma or adjointness. The zero-detection premise
remains an obligation. A later proof that uses this reduction must record the
dependencies of the published zero-detection proof it uses. This reduction
uses nothing from Aubert's Proposition 3.2.

## Sources

The target formalizes exactness detection by Jacquet modules on `Alg({I})`,
the first sentence of the proof in Aubert's 1996 erratum (printed p. 4687).
The reduction is an internal relation between published targets and
adds no literature claim. The literature content is recorded in
`RationalSupportCategoryTargets.md` and in
`RationalDetectionFiniteLengthReductionStatements.md`. The target pair, the
statement pair and every pair they import are unchanged.
