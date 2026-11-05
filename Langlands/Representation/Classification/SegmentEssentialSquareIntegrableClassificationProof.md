# The segment classification of essentially square-integrable representations

Author: Worker 320.

## Exact theorem and conventions

`Langlands.Classification.segmentEssentialSquareIntegrableClassification`
proves exactly
`Langlands.Classification.SegmentEssentialSquareIntegrableClassification.{uF,uV} F T`
from `SegmentSquareIntegrabilityStatement`. Its only outer parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
There are no additional theorem hypotheses.

With `T.topology` installed, for every `n > 0` and every actual irreducible
smooth complex representation `π` of `GL_n(F)` with carrier in
`Type (max uF uV)`, the theorem proves

```text
T.IsEssentiallySquareIntegrable π.representation
  ↔ ∃ (Δ : T.Segment.{max uF uV,uF}) (h : Δ.degree = n),
      T.IsSegmentHead Δ (h.symm ▸ π).
```

The universes `uF` and `uV` are independent. The degree equality transports
the same representation to the segment's rank. The strong head relation
includes the actual irreducible quotient map and uniqueness of its kernel.
The analytic predicate retains square-integrability of actual absolute
matrix coefficients modulo the center after a real determinant twist.
It is not defined by membership in the image of the segment construction.

Segments have positive cuspidal rank and positive length. Their increasing
products use the upper block parabolic, right translation and covariance
with the positive half modulus, with `ν = |det|_F` and
`|ϖ|_F = q^(-1)`. The special head is the quotient of the increasing
product. These are the unchanged conventions of the target and its imports.

## Published inputs

The proof applies the following Library theorems by Lean name.

| Theorem in `Langlands.Classification` | Role |
| --- | --- |
| `squareIntegrableIntegralCuspidalJacquetWordExistence` | Supplies an actual integral cuspidal Jacquet word for the given analytic square-integrable representation. |
| `integralCuspidalJacquetWordOrderedRuns` | Selects a lexicographically minimal realized word in the original permutation class and decomposes it into positive consecutive runs with nondecreasing tops. |
| `adjacentCuspidalJacquetInterchange` | Supplies the adjacent local move required by the ordered-run theorem. |
| `twoSupercuspidalNonadjacentProductIrreducible` | Supplies the nonadjacent two-cuspidal irreducibility input of that local move argument. |
| `repeatedCuspidalTripleJacquetTransfer` | Supplies the repeated-triple local move. |
| `minimalIntegralCuspidalRunsSegmentInduction` | Extracts actual strong segment factors and an actual embedding of the representation into their normalized product from the minimal runs. |
| `integralSegmentHeadScalarNorm` | Provides a common real scalar-norm parameter for all integral segments on the chosen cuspidal line. |
| `orderedIntegralSegmentInductionSquareIntegrableCollapse` | Forces the number of these ordered factors to equal one using the strict analytic scalar cone. |
| `twoSegmentHeadCommutation` | Supplies the actual two-segment product isomorphisms needed by the collapse theorem. |
| `consecutiveIntegralCuspidalWordSegmentHead` | Detects the strong segment head from the resulting single consecutive word. |
| `segmentConstituentRealTwistCompatibility` | Transports the strong head relation through actual real determinant twists. |
| `segmentSpecialEssentialSquareIntegrability` | Proves analytic essential square-integrability for every actual irreducible special segment quotient. |

The imports identify the proof modules for these declarations. In particular,
the initial-word theorem is in
`SquareIntegrableIntegralCuspidalJacquetWordProof`, the ordered-run theorem
is in `IntegralCuspidalJacquetWordOrderedRunsProof`, and the two-cuspidal
theorem is in `TwoSupercuspidalNonadjacentIrreducibilityProof`.
`SmoothRep.hasFiniteLength_of_isIrreducible` and the simple-module
nontriviality lemma provide finite length and a nonzero actual carrier.
Square-integrability itself supplies admissibility. No general admissibility
theorem for all smooth irreducibles is added as a hypothesis.

## Implemented proof

Two private lemmas organize the converse.

The first starts with a supplied minimal realized integral word written as
positive consecutive runs with monotone upper endpoints `a i` and lengths
`l i`. It also takes the run-extraction, scalar, collapse, consecutive-word
and commutation interfaces as explicit arguments. Write

```text
b i = a i - (l i - 1),
Δ i = [ν^(b i) A, ..., ν^(a i) A].
```

Run extraction supplies actual representations `X i` that are strong heads
for these segments, the degree sum, the whole normalized Jacquet quotient
and an embedding of the original representation into the normalized
induction of the `X i`. The proof packages those same factors as a
`SegmentProductDatum`; it does not select replacement representatives.

The integral coordinate equations follow from positivity of `l i` by
integer arithmetic. Apply the common scalar-norm theorem to the fixed
cuspidal datum before introducing any segment. Its one real parameter then
gives a scalar character and norm formula for each actual factor.
The collapse interface, supplied with actual commutation, the ordered
coordinates and the original analytic square-integrability hypothesis,
forces the number of runs to equal one. The flattened realized word is now
the single consecutive word. Its degree sum identifies the ambient rank,
and the consecutive-word interface gives the required strong head for the
original representation.

The second private lemma starts from any actual integral cuspidal word.
It applies the ordered-run theorem with the three published local inputs
in the table. Index the resulting list of runs by its original positions.
List membership gives positive lengths; the chain of upper endpoints gives
`Monotone a`. The proof rewrites each range-based run as a `List.ofFn` and
rewrites their concatenation as the precise flattened word used by the
first lemma. If a realized permutation of that word were lexicographically
smaller, transitivity of list permutation would contradict the selected
minimum in the original permutation class. The first lemma therefore
applies. These private lemmas are conditional organizational results; the
final theorem supplies every one of their interface arguments.

For the final converse, unfold essential square-integrability and choose
its real exponent `s`. Bundle the actual smooth representation

```text
π₀ = π.twist (T.determinantPowerCharacter n (-s)) ...
```

Its underlying action is exactly the real twist in the analytic definition.
Twisting preserves irreducibility, and the supplied normalization says
that `π₀` is square-integrable. The published initial-word theorem gives
an actual integral cuspidal Jacquet word of `π₀`.
Apply the second private lemma with all five remaining interfaces supplied
by the published run-extraction, scalar, collapse, consecutive-word and
two-segment commutation theorems. This produces a segment `Δ`, a degree
equality and a strong head relation for that same normalized representation.

Eliminate the degree equality and take the segment `Δ.twist s` for the
original representation. Apply the reverse implication of the head
biconditional in `segmentConstituentRealTwistCompatibility`, at this
segment and exponent `-s`. The required normalized head is the one already
obtained: `Segment.twist_twist`, `neg_add_cancel` and `Segment.twist_zero`
identify `(Δ.twist s).twist (-s)` with `Δ`. Dependent congruence handles
the segment equality, and the remaining equality of the transported
smooth representations is reflexive. Thus this step preserves the full
strong head relation, including kernel uniqueness. The compatibility
theorem is specialized to carrier parameter `max uF uV`, so its segment
universe and every actual carrier agree with the saturated target.

For the other implication, eliminate the supplied degree equality and
use `IsSegmentHead.isSegmentQuotient`. The published
`segmentSpecialEssentialSquareIntegrability` theorem applies to that
actual irreducible quotient and yields the required analytic predicate.
This implication forgets only the head's kernel-uniqueness clause.

## Provenance and independence

The target is Bernstein's theorem in Zelevinsky 1980, §9.3, printed p.198;
§9.1, printed p.197, fixes the special quotient convention. The registered
source is `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Zelevinsky explicitly omits the converse proof there.

Auel 2004, Theorem 6.1 and pp.18–22, gives a written converse through
Aubert duality and multisegment classification. The registered copy is
`provided-dd2424348af1ddf73426a58cb44a42985d610bade9fb26dd0da2739fbc2494d1`,
SHA-256
`3a6bcabbd0fa06a16e530cd3e7381c42742e3f1e4545316e2bf047e62afb1e65`.
The convention and correction discussion in
[the source note](../../../notes/henniart/gln-classification-sources.md)
applies to that literature route.

The present proof is an internal assembly of the published analytic and
local Jacquet-word theorems listed above. Its converse uses minimal words,
actual segment factors and the strict scalar cone. It does not implement
Auel's duality argument or rely on Zelevinsky's omitted proof.
The construction direction is supplied by the separate published analytic
construction theorem.

No multisegment exhaustion, ordered strong-head existence, quotient
coverage, tempered block uniqueness, square-integrable Langlands
classification, square-integrable exhaustion or regular exhaustion theorem
is used as a mathematical input, directly or transitively. Imported
proposition definitions do not supply proofs of those conclusions.
The generic regular-head module in the construction closure is used only
for `RegularHeadExistence.nontrivial_normalizedProductInduction`, whose
compact-section proof establishes nontriviality without an exhaustion
theorem. The Gelfand–Kazhdan contragredient reversal in two-segment
commutation provides an actual intertwining isomorphism.
The singleton-socle imports also contain the conditional ordered-head
assembly lemmas. Those conditional conclusions are never applied here;
the reused declarations from that module establish only irreducibility
of a one-dimensional representation and the explicit rank-zero product
linear equivalence. The singleton-socle construction uses the elementary
fact that an irreducible subrepresentation of an irreducible representation
is its strong socle.
All imports retain the actual maps and subquotients used by their
published statements.
