# Joint detection by the actual one-step mirabolic minus functors

Authors: Worker 499 audited the published dependencies and assembled this proof.
Worker 237 supplied the tested exact-interface wrapper in the proof task.
The underlying published vanishing theorem is Worker 1025's work and is reused
as a Library dependency.

The theorem
`Langlands.Derivative.mirabolicOneStepDetection.{uF,uV}` proves exactly the
published proposition
`Langlands.Derivative.MirabolicOneStepDetection.{uF,uV} F T`.
Its complete outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The field and representation-carrier universes remain independent.

After installing `T.topology`, the proof introduces the character, rank and
representation by a lambda and applies
`Langlands.Derivative.Mirabolic.subsingleton_of_psiMinus_phiMinus.{uF,uV} T ψ n A`.
The conclusion and both antecedents are definitionally the body of the target.
No transport of representations, replacement quotient or additional premise is
introduced. The only direct project imports are the published target statement
and `Langlands.Representation.Derivative.MinusVanishing`.

For every nontrivial continuous unitary additive character `ψ`, every `n : ℕ`,
and every `A : SmoothRep.{0,uF,uV} ℂ
(GeneralLinear.mirabolic (n+1) F.Carrier)`, the result says

```lean
Subsingleton ((Mirabolic.psiMinus T (n+1)).obj A) →
Subsingleton ((Mirabolic.phiMinus T ψ n).obj A) →
Subsingleton A
```

The source is the actual `P_(n+2)`; the outputs belong respectively to
`GL_(n+1)` and `P_(n+1)`. The same `ψ` is used throughout. Both outputs are the
existing relation-span quotients, with inverse-half determinant output twists.
Those twists preserve the quotient carriers. No identification of determinant
norm with a Haar automorphism modulus is used.

The assertion covers arbitrary smooth representations, including infinite
dimension, infinite length and nonadmissible representations. At `n=0` it is the
`P_2` step. There is no finite-length, admissibility, Artinianity, irreducibility,
homogeneity, exactness, filtration, plus-functor, segment, product, head, socle
or classification premise. The separate `P_1 → GL_0` boundary and the iteration
bridges for higher derivatives are not conclusions of this theorem.

## Source and implemented argument

The original source is Bernstein–Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
Proposition 3.2(e), printed p.451 / one-based PDF page 12, gives

```text
0 → Φ⁺Φ⁻ → Id → Ψ⁺Ψ⁻ → 0.
```

Joint detection is a derived consequence: vanishing of both minus outputs makes
both outside terms zero, so exactness forces the middle representation to be
zero. Section 3.5, printed p.452 / PDF page 13, explains the iterative context.
Worker 499 read both original pages, including their rendered images. The
source sends the proof of the exact sequence to its reference [1], §5.
The present proof does not assume that exact sequence or formalize that
reference. It reuses the independently proved direct argument below.

The public source/errata guidance and the relevant public independence note
were checked, together with a bounded search of the original publication's
Numdam record and targeted correction searches. No applicable correction to
these passages was located. This reports the checks made and does not assert
that no erratum exists.

The implemented mathematics inside `MinusVanishing` is as follows.

1. Subsingleton quotient carriers imply that the trivial-character and
   last-coordinate-character relation spans are the whole source. The trivial
   parameter is covered by `Ψ⁻`. Every nonzero coordinate row is the last row
   of an invertible matrix. Conjugation by its Levi element transports the
   `Φ⁻` relations to the relations of that row character. Consequently every
   vector lies in the relations of every coordinate character.
2. Smoothness supplies an open subgroup fixing a chosen vector `x`. Lattice
   cofinality gives a radical lattice box fixing `x`. The increasing radical
   boxes exhaust the radical. The proved
   `Jacquet.Localization.eventually_characterAverage_eq_zero` then annihilates
   `x` at some level for each coordinate character.
3. Character agreement on a radical box is controlled by the dual lattice.
   Compactness of a fixed dual box gives a finite subcover of character
   neighborhoods. Taking the largest of their levels and using monotonicity
   of vanishing gives a single level at which all characters in that dual
   box annihilate `x`.
4. Finite quotients of the radical box and of the dual box reduce the average
   identities to finite sums. Character orthogonality kills the nontrivial
   cosets. The annihilator lemma identifies the trivial coset with the box
   fixing `x`. The remaining scalar is a ratio of positive finite
   cardinalities, hence is nonzero in `ℂ`; therefore `x=0`.
5. Every vector is zero, so the source carrier is a subsingleton.

This argument needs finite orbits and finite lattice quotients for individual
smooth vectors, not finite dimension or finite length of the representation.
It proves only the vanishing implication. Exactness, adjunction, a derivative
filtration and the stronger highest-derivative pairing assertions are not
supplied by this wrapper.

## Published inputs and proof provenance

Worker 499 fetched the following exact publication records and inspected their
independent acceptance and publication information. These records establish
provenance; the Lean proof imports declarations by module name.

| Published input | Independent acceptance and publication | Use here |
| --- | --- | --- |
| `MirabolicOneStepDetectionStatement`, `16210eb0-9f2d-4d0e-a4bf-17ad694f9a66`, Worker 237 | Reviewer 4928; `lean.statement@1`; commit `6789e5106aba61566887427750f5444a494d5879` | The unchanged Prop-valued target, not a proof input. |
| `MinusVanishing`, `c6026915-8731-45a8-bd21-ef1ac39654b8`, Worker 1025 | Reviewer 4480; `lean.definition@1`; commit `771cfc69d1ff795522e29cdead1b7c40f1a1c308` | The proved auxiliary theorem `subsingleton_of_psiMinus_phiMinus`. Its semantic acceptance explicitly checks this theorem's direct proof and independence. The record is an internal definition/helper publication, not an exact-target `lean.proof` receipt for the present statement. |
| `MirabolicLatticeBox`, inherited repository helper in `2279aa64-eb04-4afa-89a9-1ea9ac87cbe2`, Worker 440 reusing Worker 806 | Reviewer 3969; `lean.proof@1`; commit `b0ef093b63d0f0c27bb690dca12820c991756955` | Finite lattice quotients, lattice cofinality, duality and character sums. The acceptance explicitly checks the inherited helper. The accompanying `phiMinusIrreducible` theorem is not imported or used. |
| `Jacquet.CharacterAveraging`, repository helper in `faa65dca-289a-4fb5-941a-b5e1200ff62e`, Worker 831 | Reviewer 4000; `lean.definition@1`; commit `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` | Compact twisted averages, their finite quotient formula and eventual annihilation of relations. These helper proofs were included in the independent semantic review. Neither the conditional deformation assembly nor its Whittaker uniqueness premise is used. |
| `PadicAdditiveConductorProof`, `8f35e474-ea64-4213-b49c-80f70e559886`, Worker 568 | Reviewer 2908; `lean.proof@1`; commit `6543e70ef8c82ed8535a0f9fd06c59ed896bc738` | The proved integer-ring annihilator and conductor shift, with the convention `additiveLattice m = π^(-m) O`. |
| `ZeroRowLastRowCutoffProof`, `c1ca32b0-5a13-4540-95ca-4b21576ff387`, Worker 252 | Reviewer 3434; `lean.proof@1`; commit `6d91111e6f9b7a27124b1de32a4984bbdd222a61` | Only the elementary lemma `T.mem_additiveLattice_of_forall_mul_eq_one` is needed by `MirabolicLatticeBox`. The Whittaker cutoff conclusion is not a proof input. |

The target, `PadicAdditiveConductorProof` and `MinusVanishing` pairs match
their accepted frozen pairs byte for byte. `MirabolicLatticeBox` is inherited
from the accepted candidate's Library base
`f4b4c23a7ab185fd0e15d16d2864b818a083a194`, rather than part of its file
delta; both inherited files match that base and the current public base.

Two accepted helpers have undergone public import extractions. Worker 499
compared the current code with the frozen accepted sources:

- `CharacterAveraging` now imports `Compact.OrbitMeanTranslation`, drops its
  local translation-invariance lemma and calls `Compact.orbitMean_apply`.
  The current shared proof identifies the two orbits by translation and
  applies the normalized finite-sum expression. It was moved from
  `Jacquet.ExactProof`; that exactness module is not imported. All other
  character-averaging proof code is unchanged.
- `ZeroRowLastRowCutoffProof` now imports `PadicLatticeTopology`. The compactness
  and openness lemmas were moved there with identical theorem bodies.
  The annihilator theorem actually used here has an identical statement and
  proof in the accepted frozen source and the current Library.

These are reorganizations of elementary proofs, not uses of their former
consumers. Current pairs were independently compared with the immutable public
base below; no private replacement or pending result supplies an input.

## Mathematical dependency audit

The audit follows actual proof uses as well as imports. It was made by Worker
499 for this task; earlier workers' private audits were navigation aids only.
The trusted operator message
`/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md`
was read in full. It permits a fully proved general BZ77 route, requires
independently accepted and published derivative inputs, and excludes circular
segment/classification dependencies. The only derivative theorem used by the
wrapper is the published `MinusVanishing` theorem audited above.

The complete project closure partitions as follows.

- **Local fields and their normalizations.** `LocalField.Definitions`,
  `Canonical`, `Topology` and `Normalization` implement the supplied p-adic
  field structures, valuations, integer rings, uniformizers and normalized
  absolute values. Their proofs use field and valuation theory and Mathlib
  topology. Their canonical constructions occur as imports of the general
  linear topology API; the representation proof itself installs the supplied
  `T` throughout. These files contain no derivative or classification input.
- **Actual matrix groups.** `Group.GL.Basic`, `RankMaps`, `UpperUnipotent`,
  `Mirabolic` and `MirabolicRadical` supply matrix units, block inclusions,
  radical coordinates, Levi multiplication and conjugation identities.
  `NormalizedCharacter` constructs determinant norm characters.
  `Nonarchimedean` and its statement concern compact open bases.
  `Group.GL.Padic` derives the matrix-unit topological-group, Hausdorff and
  local compactness certificates from the supplied local-field data and
  Mathlib instances. It introduces no representation-theoretic conclusion.
- **Representation, smoothness and twists.** `Category`, `Smooth`,
  `Dual`, `MatrixCoefficient` and `Twist` provide actual modules, actions,
  open fixing subgroups, quotient/pullback smoothness, algebraic duals and
  scalar twists. Their proofs are formal action, linear-map and
  open-subgroup arguments. Admissibility definitions and preservation
  results occur in this import closure, but no admissibility hypothesis
  on `A` is used. No finiteness or classification theorem is imported.
- **Actual minus quotients.** `Jacquet.Coinvariants`, `Localization` and
  `SmoothTwist` form actual relation-span quotients, descend the stabilizing
  action and prove smoothness. `MirabolicCharacter` gives the positive
  last-coordinate character and its stabilizer. `MirabolicMinus` forms
  precisely the target functors and their carrier-preserving
  inverse-half determinant twists. No exactness, plus-functor identity or
  derivative detection premise occurs in these constructions.
- **Finite averaging.** `Compact.Definitions`, `FiniteMean`,
  `ProjectionStatement`, `ProjectionProof` and `OrbitMeanTranslation`
  use finite orbits of a smooth vector under a compact open subgroup.
  Compactness and open stabilizers make these orbits finite; the
  projection identities and naturality follow from permutations and
  equal-fiber counting. `CharacterAveraging` twists by the inverse
  character, applies these means and proves annihilation of a finite
  relation expression along an exhaustion. Its later functional
  extension and uniqueness-conditioned spanning theorem are not used.
  These are elementary finite averages; no representation-space
  topology, invariant measure or irreducibility is assumed.
- **Conductor and lattice geometry.** `HarmonicAnalysis.Basic`,
  `Conductor`, `PadicAdditiveConductorProof` and `PadicLatticeTopology`
  give the actual nontrivial continuous character, its conductor and
  lattice annihilator, and the compactness and openness of lattices.
  `PadicScalarHaarScalingProof` supplies the integer-ring topology
  lemmas used by the lattice topology proof. Its measure-scaling
  conclusion is not used in detection. Imported harmonic statement
  definitions, including `PadicHaarScalingStatement` and
  `LocalFactor.Harmonic.Statement`, are not treated as hypotheses or
  proofs. `MirabolicLatticeBox` proves finite lattice quotients by an
  open subgroup of a compact group, obtains cofinality from valuation
  bounds and a finite product basis, obtains dot-product duality from
  the scalar annihilator by testing one coordinate, and proves finite
  nontrivial-character sums vanish by translation.
- **Transitive Rankin–Selberg imports.** `ZeroRowLastRowCutoffProof`
  supplies the scalar annihilator extension by multiplication with a
  uniformizer power and the proved integer-annihilator theorem.
  Its other imports include actual last-row matrix geometry,
  compact-open indicator functions, matrix coefficients and
  `QuotientIntegrals`; the latter in turn imports
  `Analysis.Local.QuotientMeasure`. These are lower constructions and
  quotient-measure identities. No Rankin–Selberg factor theorem,
  Whittaker uniqueness conclusion, segment formula or classification
  result occurs as an input to the used annihilator lemma.
- **Vanishing.** The coordinate characters, radical boxes, Levi
  transport, compact dual-box argument and finite Fourier sum inside
  `MinusVanishing` give the five-step proof described above. Each
  mathematical input is provided by the elementary lower groups just
  audited. In particular there is no assumption of the BZ77 exact
  sequence and no use of any highest-derivative or segment consumer.

Thus the direct proof has no path to any excluded mathematical conclusion,
proof successor or downstream consequence. Keyword checks alone would not
establish that fact: the proof roles above explain why the lower constructions
are independent of those conclusions.

## Complete structural import audit

The audit base is Library commit
`d54bbb9c881aa001e78c70a31a3a7bcb88affb43`.
Worker 499 recursively parsed all project imports, stripping nested Lean
block comments and line comments. For each reached module, both `.lean`
and same-stem `.md` were nonempty, byte-identical to that public base,
and SHA256-verified against its immutable manifest.

`MinusVanishing` has 69 transitive project dependencies, hence 70 modules
including itself. The target has 50 transitive project dependencies.
The new proof imports their union of **71 project modules**; the new proof
module itself is not counted. These counts describe this base and include
the shared import extractions above.

The full sorted union is listed below. Every listed name denotes both checked
files by replacing dots with slashes and adding `.lean` or `.md`.
Mathlib imports are supplied by the pinned environment and are not counted as
project modules.

```text
Langlands.Analysis.Local.QuotientMeasure
Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.LocalFactor.Harmonic.Statement
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicOneStepDetectionStatement
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.Nonarchimedean.Subgroup
```

The code scan found no excluded task identifier or declaration name and no
proof holes, new axioms or unsafe execution commands. The mathematical proof
audit above also checks the conclusions represented by those names. The
only textual exclusion hits in inherited paired prose state restrictions:
`MirabolicMinus.md` denies use of square-integrable classification and generic
segment-product uniqueness; the target Markdown discusses its
highest-derivative consumer and the operator-paused exactness task.
They are not proof inputs.

## Full independence boundary

The following is the full inherited exclusion union from this proof task,
retained verbatim as an audit boundary. References to a consumer's proof also
apply to every prerequisite, including this theorem. No lower split was
needed. This proof additionally excludes the highest-derivative pairing
consumer `a925b519-9bb9-4927-873e-ad322d41328e` and all its proof successors.
It neither uses nor duplicates the operator-paused minus-exactness work
`b65bc667-6951-4bd5-82af-10fb7046df7f`, and has requested no resumption.


This is the BZ77-only upstream detection clause for mirabolic strong-indecomposability statement task `ff4738d8-47e3-433b-bedc-629bc2d492a7`, ordered-socle proof task `23189526-80b0-4828-a6d4-7ebec2cbeef5`, and nonadjacent two-supercuspidal product task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`. It does not duplicate or replace the combined Ze80 section 5.4 reduction statement. Do not use that combined reduction or its strong-indecomposability conclusion to prove detection. Do not use either the nonadjacent product conclusion or the full two-supercuspidal product-structure conclusion of `ab61f565-1427-4746-ba77-46097563e962`, including its adjacent composition/Jacquet conjuncts. The proof route must be general BZ77 derivative theory and independent of these consumers.

The trusted operator conditions recorded for the nonadjacent consumer are in `/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md` (sender_role operator); read that file completely. They allow a fully proved BZ77 derivative route and forbid using Ze80 segment derivative formulas or circular results. Every lower derivative result later used must have an independently accepted and published proof. A citation, unproved proposition, draft or pending task is not a proof input. Preserve the following full union of exclusion sets, including mathematical conclusions, exact proof successors and transitive dependencies, in all later proof and lower prerequisite tasks.

Do not use conclusions, proof successors or transitive proof dependencies of ordered-socle existence `23189526-80b0-4828-a6d4-7ebec2cbeef5`, socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`, analytic segment classification `aca8805b-054f-4d56-8045-12db7f623404`, unlinked segment-socle product irreducibility `23e98d90-6055-4e35-91a9-b0f5d8a84961`, the final segment-socle irreducibility criterion `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, the special-head product irreducibility criterion `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, special-head exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness `52e97845-36bb-457d-b76f-70753334b88c`, `SquareIntegrableLanglandsClassification` / `1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`, `GenericSegmentProductUniqueness` / `30341ae4-65f2-4a0e-9283-763db01a409e`, ordered special-segment conversion `8252833d-c269-41a9-824c-5879e531b23b`, or forward special-segment essential square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`. Preserve this full exclusion set in later proof tasks and lower splits. Shared lower inputs need their own independence audit.

Additional nonadjacent-consumer exclusions (the references to "this proof" mean that consumer and every prerequisite, including detection):

Neither this
proof nor any prerequisite may depend directly or transitively on the following
tasks, their mathematical conclusions, proof successors or downstream
consequences:

- Individual special-head/reverse-socle existence
  `67279e36-f3c2-42e3-9302-11729784042e`.
- Individual segment-socle/reverse-head existence
  `4ca79bbd-589e-476b-9f65-661e799984b5`.
- Analytic segment classification
  `aca8805b-054f-4d56-8045-12db7f623404`.
- Forward special square-integrability,
  `SegmentSpecialEssentialSquareIntegrability`, and
  `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`.
- Multisegment special-head exhaustion
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`.
- Ordered strong-head existence
  `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`.
- Quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`.
- Ordered conversion `8252833d-c269-41a9-824c-5879e531b23b`.
- Tempered uniqueness `52e97845-36bb-457d-b76f-70753334b88c`.
- `SquareIntegrableLanglandsClassification` and
  `1cb45da2-7007-4351-a694-594fb148b8d1`.
- Square-integrable exhaustion
  `cd8ab97c-0b78-4bce-97c4-d307a28159a4`.
- Regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`.
- Special-head product irreducibility
  `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`.
- `GenericSegmentProductUniqueness` and
  `30341ae4-65f2-4a0e-9283-763db01a409e`.
- `OrderedMultisegmentSocleExistence` and
  `23189526-80b0-4828-a6d4-7ebec2cbeef5`.
- `MultisegmentSocleExhaustion` and
  `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`.
- `SegmentSocleProductIrreducibility` and
  `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`.
- Adjacent socle commutation
  `e3634665-571b-4852-9f4c-bab8a1053434`.
- `SegmentFullJacquetFormula`, its statement/successor-arrangement task
  `ed48ae06-964c-4c84-9e62-978f5a953ca7`, and its exact proof successor.
- `SegmentHeadJacquetFormula` and
  `55ad1e10-62d8-46b7-a081-909ef0056426`.
- `SegmentSocleJacquetFormula` and
  `b95105c6-f8bb-4641-ae53-2f49d1e7f034`.
- `SegmentSpecialJacquetExponentNormFormula` and
  `92aea10f-62ac-4e0b-bd4a-9a80909797c5`.

Preserve also the full-formula consumer's additional restrictions: do not
use Ze80's segment derivative formulas (§3.5 or §9.6), and do not assume any
derivative result (including BZ77's) without a proof accepted and published
under the operator conditions above; do not assume a segment product
irreducibility criterion (Ze80 4.2 or 9.7), an analytic or
square-integrability result (Ze80 9.3), or a classification or exhaustion
theorem. Ze80 Theorem 4.2's linked-pair converse rests on §2 and cannot
prove Proposition 1.11 circularly. Carry these exclusions unweakened to every
prerequisite and document the import and mathematical proof-dependency audit
in the final proof Markdown. Shared lower constructions may be reused only
after their independence is checked.

Audit the full transitive project import closure against the public Library and record it completely in the paired Markdown. Do not use Ze80 section 3.5 or 9.6, or the segment-socle part of task `8e5b4563-0365-41c7-b134-70f2a0b36292`; this detection assertion requires no segment or cuspidal derivative formula at all. Shared lower constructions may be reused only after independence checks.

Carry this full exclusion union unweakened to every lower split of this proof.


## Validation

The prepared environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Only the new proof pair is submitted. All existing Library pairs, including
the target and its entire dependency closure, remain unchanged.
Development compilation and declaration inspection are distinct from
independent semantic acceptance, exact-target validation and publication.

Development check `a5586d38-db44-4a31-af53-63906cb2ff2f` compiled the final
proof and a private declaration-inspection module with zero errors and zero
warnings. The complete unapplied type printed as

```lean
∀ {p : ℕ} [Fact (Nat.Prime p)] (F : PadicField.{uF} p)
  (T : F.TopologicalData), MirabolicOneStepDetection.{uF,uV} F T
```

The inspection reports independent level parameters `uF`, `uV` and exactly
`propext`, `Classical.choice`, `Quot.sound`. Its generic theorem-inspection
mode does not run the submission's exact-target check; the proof candidate's
machine validation supplies that separate check. The private diagnostic
module is excluded from staging. A full hash comparison also found all
11,712 pre-existing public-base files unchanged.
