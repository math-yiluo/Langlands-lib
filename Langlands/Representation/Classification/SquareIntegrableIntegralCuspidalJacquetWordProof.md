# Actual integral cuspidal Jacquet words for analytic discrete series

Authors: Worker 78 (integer-orbit argument and final assembly) and Worker 158
(analytic interfaces, scalar and cone proofs, and the finite complementary
prefix obstruction). Other authors' published results enter by import.

The theorem
`Langlands.Classification.squareIntegrableIntegralCuspidalJacquetWordExistence`
proves the unchanged published proposition
`Langlands.Classification.SquareIntegrableIntegralCuspidalJacquetWordExistence.{uF,uV} F T`.
Its complete outer telescope is

```lean
∀ {p : ℕ} [Fact p.Prime] (F : Langlands.PadicField.{uF} p)
  (T : F.TopologicalData),
  Langlands.Classification.SquareIntegrableIntegralCuspidalJacquetWordExistence.{uF,uV} F T
```

The field and carrier universes are independent. The supplied `T` determines
the topology, residue-normalized determinant twists, upper normalized
induction and inverse-half-modulus upper Jacquet functors throughout.
The only representation hypotheses are irreducibility and the original
analytic `T.IsSquareIntegrable`. The input and the supercuspidal factors have
carriers in `Type (max uF uV)`.

The conclusion supplies a positive rank `m`, an actual supercuspidal
representation `A`, and a nonempty ordered integer list `w`. It retains an
actual external tensor as an actual `SmoothRep.IsSubquotient` of a normalized
upper Jacquet module. Its rank-indexed class equalities identify every
original factor with the corresponding integer determinant twist of `A`.
The base is one of those original factors and need not be unitary.

## Implemented proof

Start with positive rank `n`, an irreducible actual smooth representation
`π`, and its analytic square-integrability hypothesis. Simplicity of
`π.representation.asModule` gives finite length. Admissibility is extracted
from `hsq.isAdmissible`; the analytic predicate, including its matrix
coefficients and central-quotient Haar measures, is unchanged.

`CuspidalSupport.cuspidalTensorJacquetQuotientExistence` supplies a block
shape `B` and actual supercuspidal factors `C i` whose external tensor is a
quotient of the actual normalized Jacquet module. Its quotient-to-subquotient
map gives the occurrence used below. Positive total rank makes `B.length`
positive.

Apply `cuspidalTensorRealParts` once to this original family. It supplies
actual scalar characters `c i` and real numbers `t i` with

```text
‖c i a‖ = |a|^x_i,       x_i = -((B.size i : ℝ) * t i).
```

`permutedCuspidalTensorCone` uses these same characters and coordinates for
each actual permuted occurrence. Its conclusion is
`Exponents.IsPositiveRootCone (x ∘ e)`: zero full sum and strictly positive
proper prefix sums. Every individual rank weight remains attached to its
original label. The proof makes no second choice of real parts after a
permutation.

The private integral-orbit argument works in
`Σ d, SupercuspidalClass (n := d)`. Write
`c_i = ⟨B.size i, (C i).isoClass⟩`. Integer twist is the published real
determinant twist evaluated at an integer. Its zero and addition identities
follow directly from the published twist laws.

Take the original label `i₀ = 0` as base, and let `S` be precisely the
labels with `c_i = ν^z c_i₀` for some integer `z`. It contains `i₀`. A
label outside `S` cannot differ by a unit twist in either direction from
a label in `S`: applying the inverse unit twist and adding integer exponents
would place it in `S`.

For each such cross-pair,
`twoSupercuspidalNonadjacentProductIrreducible` proves irreducibility of
its actual normalized two-block product. The binary product bridge
identifies this with `T.binaryNormalizedProductFunctor`; then
`irreducibleBinaryProductCommutation` supplies the actual reversed-product
isomorphism with the literal total-rank cast. This covers possibly unequal
ranks without assuming equality of their block sizes.

Apply `cuspidalJacquetSubsetGrouping` with the published
`adjacentCuspidalJacquetInterchange` twice: first put `S` first, then put its
entire complement first in a second occurrence. Each result keeps every
original factor, including repetitions and all complementary integral
orbits. The grouping proof changes only their positions by successive
allowed adjacent interchanges.

If the complement is nonempty, the two actual occurrences yield strict
cones for two permutations of exactly the same vector `x`.
`complementaryPrefixConeObstruction` identifies the corresponding proper
prefix sums with the sum over `S` and the sum over its entire complement.
Both would be positive, while their sum is the zero full sum. This
contradiction proves that every original label lies in `S`.

Choose integer witnesses `z i`, take
`m = B.size i₀`, `A = C i₀`, and `w = List.ofFn z`. Positive block size
gives `m > 0`; positive block count gives `w ≠ []`. The witnesses are
already the required dependent rank/class equalities. The final word uses
the original actual Jacquet occurrence, rather than either intermediate
permutation. The closing theorem discharges the private assembly's binary
premise with the published unconditional proof at universes
`{uF, max uF uV}`. No theorem-valued premise remains.

## Provenance and source boundary

This is a derived proof of the published actual-word proposition.
The source comparison is recorded in
[the statement's Markdown](SquareIntegrableIntegralCuspidalJacquetWordStatement.md):
Jantzen, *On Square-Integrable Representations of Classical p-adic Groups*
(2000), the first claim in the converse proof of Theorem 2.3.1, printed
p.549 (PDF p.11), asserts containment of cuspidal support in one
real-shifted integral cuspidal line. The registered source is
`jantzen-2000-square-integrable-classical-i`, SHA256
`539eee93dd339c42bf6d065bbb1969ab0e2c6c54699c5b4447a2166a3ddf9428`.

The implemented proof establishes the actual finite realization separately
and retains it through the argument. It does not assume the source's support
claim or replace an actual occurrence by a support-set equality. It chooses
an original actual factor as base, so it needs neither a unitary base nor a
common real shift. The finite grouping and complementary-prefix argument
handles an arbitrary finite number of integral orbits.

## Direct and transitive mathematical dependency audit

The audited inputs have the following roles. Linked proof accounts explain
the implemented lower arguments, including the inputs they themselves use.

| Input | Implemented route and independence boundary |
| --- | --- |
| [Actual initial tensor quotient](../CuspidalSupport/CuspidalTensorJacquetQuotientProof.md) | Maximal block-count nonzero Jacquet descent gives Levi-quasicuspidality. Compactness of the parabolic quotient gives finite generation and a maximal proper subrepresentation. The actual irreducible quotient is admissible by compact-open projections, Cartan-gap vanishing and scalar Schur. Actual product-Levi factorization supplies the tensor and supercuspidal factors, and composing its equivalence with the quotient map gives a genuine surjection. No support classification supplies this occurrence. |
| [Nonadjacent two-supercuspidal irreducibility](TwoSupercuspidalNonadjacentIrreducibilityProof.md) | The BZ77 derivative argument uses exactness, detection, highest-derivative pairing, supercuspidal derivatives and the complete Leibniz filtration. A proper subobject or quotient has zero top derivative; highest pairing contradicts the invariant-form length bound. Supercuspidal duality and integral twist freeness exclude the possible intermediate pairings. Every derivative premise is discharged by a published proof. There is no global disjoint-support or segment-product irreducibility input. |
| [Binary commutation](IrreducibleBinaryProductCommutationProof.md) | Inverse transpose reverses the actual normalized product. Gelfand–Kazhdan and natural induction/tensor smooth duality identify the double pullback with the original product. Explicit block and rank-cast identities give the unequal-rank binary endpoint. Only irreducibility of the original product is assumed, and it is supplied here by the preceding input. |
| [Actual adjacent interchange](AdjacentCuspidalJacquetInterchangeProof.md) | Exact refined Jacquet filtrations extract an actual irreducible coarse constituent; admissible product factorization and actual tensor subquotient extraction retain all factors. The cuspidal constituent quotient theorem, concrete first adjointness and nonzero evaluation transfer the selected pair through its irreducible commuting induction. Exactness, normalized transitivity and ordered tensor comparison reconstruct the reversed fine occurrence. |
| Lower geometric and finite-length results in that interchange | Radical coinvariant exactness is proved by compact averaging. Quotient lifts and radical factorization prove transitivity, with the inverse half-moduli multiplying correctly. Ordered flattened comparison checks the actual block embeddings and determinant modulus. Jacquet finite length follows by induction on the refinement deficit, quasicuspidal compact-coefficient splitting and lengths of proper refined Jacquet modules; it is not a decomposition by global cuspidal supports. |
| [Finite subset grouping](CuspidalJacquetSubsetGroupingProof.md) | Finite minimization of the sum of selected labels' positions ensures that no outside-inside boundary remains. Each allowed adjacent swap preserves the actual occurrence. The conclusion retains all original labels and supplies the exact prefix membership equivalence. The local pair hypotheses are discharged here only for opposite sides of `S`. |
| [Original scalar characters and real parts](../Exponents/CuspidalTensorRealPartsProof.md) | Actual supercuspidal real unitarization comes from Schur central characters, real powers, Harish-Chandra compactness on the determinant-unit subgroup and a Haar coefficient-product integral defining a positive form. The unitary central character of the twisted object is untwisted to a character of the original factor. Pure-tensor scalar action and finite-product norms give the individual rank weights. No common-line assertion is used. |
| [Strict actual Jacquet cone](../Exponents/SquareIntegrableActualJacquetConeProof.md) | Compact averaging detects an ordinary scalar character in the full transpose of the actual subquotient presentation. Finite fixed-space decomposition converts it to a nonzero generalized Jacquet vector. The analytic strict GL exponent criterion, scalar compatibility on constant block scalars and the real-part/cone equivalence give strict prefix inequalities and zero full sum. |
| Transitive strict Casselman input | `glSquareIntegrableExponentCriterion` transports the actual one-block Levi to GL and applies the independently proved refined upper strict chamber necessity. Its imported converse is the coefficient L2 summability proof using strict exponential margins and Cartan volume bounds. Central-character reduction uses actual quotient Haar existence and scalar uniqueness. These are local Jacquet and analytic estimates. |
| [Permutation scalar adapter](../Exponents/PermutedCuspidalTensorConeProof.md) and [finite complement obstruction](../Exponents/ComplementaryPrefixConeObstructionProof.md) | The adapter permutes the same original characters and rank weights, proves tensor nonzeroness by a tensor basis, and applies the strict actual cone theorem. The obstruction is finite reindexing, complementary sums and real arithmetic. Neither constructs support data or assumes a classification conclusion. |

The binary proof's six Lean/Markdown pairs and five derivative entry proof
accounts were read. Its corrected source normalization distinguishes BZ77's
`Delta_P = nu^-1` and inverse pairing convention from the Library's positive
`|det|` covariance. The corrected independently approved public candidate is
`98cc1114-db18-414e-8ad5-ddb3f559e47d`; all twelve published file hashes
match that audited candidate. The exactness, highest-pairing/detection,
supercuspidal-derivative and Leibniz proof publications were separately
verified. They supply general derivative theory, not a segment derivative
formula or classification theorem.

At Library base `a5dff2ff93bd3637a67ee8847f67f811efc82f01`, recursive native
source traversal from this unconditional proof resolves **1,071 project
modules** and 314 distinct direct external imports. There are no missing
or unusual imports or missing Markdown companions. All 1,070 imported
project Lean/Markdown pairs are byte-identical to the published Library.
The main proof pair is the only addition. The scan covers every transitive
project import, not merely the entry module's direct imports.

The scan finds none of the following conclusions, closing proof names,
named statement/proof modules or task identifiers in any closure Lean file:

| Excluded family | Task |
| --- | --- |
| Analytic segment classification | `aca8805b-054f-4d56-8045-12db7f623404` |
| Multisegment special-head exhaustion | `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` |
| Ordered strong-head existence | `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` |
| Ordered quotient coverage | `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` |
| Tempered-block uniqueness | `52e97845-36bb-457d-b76f-70753334b88c` |
| `SquareIntegrableLanglandsClassification` | `1cb45da2-7007-4351-a694-594fb148b8d1` |
| Square-integrable Langlands-head exhaustion | `cd8ab97c-0b78-4bce-97c4-d307a28159a4` |
| Regular tempered Langlands-head exhaustion | `bf433f0a-921a-428c-b0c0-6475438125ac` |

The closure includes the shared lower `IntegralCuspidalJacquetWord`
definition. Other segment-named imports provide definitions and elementary
scalar-character calculations: `SegmentConstituentCentralCharacterProof`
computes scalar actions on actual induced tensors and transfers them through
given injective or surjective intertwiners. Its algebraic constituent helpers
transport twisting and prescribed characters; they assert no existence or
classification. Neighboring tempered proposition definitions supply no
theorem premise here.

The whole-source scan is a conservative check of named dependencies; the
mathematical routes above explain why the proof also assumes none of the
excluded conclusions under another name. In particular, global
disjoint-support irreducibility, general ordered quotient coverage, full
multisegment classification and the desired one-line support assertion are
not inputs. The one-line conclusion is proved by the integer-orbit and
complementary-cone argument.

## Development checks

Compilation and theorem inspection succeed in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with zero errors or warnings. The
unapplied theorem constant assigns directly to the complete target telescope
displayed above, preserving parameter order and independent `uF,uV`.
Inspection reports only `propext`, `Classical.choice` and `Quot.sound`.
These development checks are separate from the candidate's required
exact-target machine validation, independent semantic review and publication.
