# Joint detection by the actual one-step mirabolic minus functors

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
`Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`
in the central library.
Proposition 3.2(e), printed p.451 / one-based PDF page 12, gives

```text
0 → Φ⁺Φ⁻ → Id → Ψ⁺Ψ⁻ → 0.
```

Joint detection is a derived consequence: vanishing of both minus outputs makes
both outside terms zero, so exactness forces the middle representation to be
zero. Section 3.5, printed p.452 / PDF page 13, explains the iterative context.
Both original pages were read, including their rendered images. The
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

The following published inputs were checked; the Lean proof imports
declarations by module name.

| Published input | Library commit | Use here |
| --- | --- | --- |
| `MirabolicOneStepDetectionStatement` | `6789e5106aba61566887427750f5444a494d5879` | The unchanged Prop-valued target, not a proof input. |
| `MinusVanishing` | `771cfc69d1ff795522e29cdead1b7c40f1a1c308` | The proved auxiliary theorem `subsingleton_of_psiMinus_phiMinus`. |
| `MirabolicLatticeBox` | `b0ef093b63d0f0c27bb690dca12820c991756955` | Finite lattice quotients, lattice cofinality, duality and character sums. The accompanying `phiMinusIrreducible` theorem is not imported or used. |
| `Jacquet.CharacterAveraging` | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` | Compact twisted averages, their finite quotient formula and eventual annihilation of relations. Neither the conditional deformation assembly nor its Whittaker uniqueness premise is used. |
| `PadicAdditiveConductorProof` | `6543e70ef8c82ed8535a0f9fd06c59ed896bc738` | The proved integer-ring annihilator and conductor shift, with the convention `additiveLattice m = π^(-m) O`. |
| `ZeroRowLastRowCutoffProof` | `6d91111e6f9b7a27124b1de32a4984bbdd222a61` | Only the elementary lemma `T.mem_additiveLattice_of_forall_mul_eq_one` is needed by `MirabolicLatticeBox`. The Whittaker cutoff conclusion is not a proof input. |

The target, `PadicAdditiveConductorProof` and `MinusVanishing` pairs match
their published pairs byte for byte. Both `MirabolicLatticeBox` files match
the Library base `f4b4c23a7ab185fd0e15d16d2864b818a083a194` and the audit
base below.

Two of these helpers have since undergone public import extractions. The
current code was compared with their sources as first published:

- `CharacterAveraging` now imports `Compact.OrbitMeanTranslation`, drops its
  local translation-invariance lemma and calls `Compact.orbitMean_apply`.
  The current shared proof identifies the two orbits by translation and
  applies the normalized finite-sum expression. It was moved from
  `Jacquet.ExactProof`; that exactness module is not imported. All other
  character-averaging proof code is unchanged.
- `ZeroRowLastRowCutoffProof` now imports `PadicLatticeTopology`. The compactness
  and openness lemmas were moved there with identical theorem bodies.
  The annihilator theorem actually used here has an identical statement and
  proof in the source as first published and the current Library.

These are reorganizations of elementary proofs, not uses of their former
consumers. Current pairs were compared with the immutable public
base below; no private replacement or unproved result supplies an input.

## Mathematical dependency audit

The audit follows actual proof uses as well as imports. The conditions it
checks permit a fully proved general BZ77 route, require published derivative
inputs, and exclude circular segment/classification dependencies. The only
derivative theorem used by the wrapper is the published `MinusVanishing`
theorem audited above.

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
any proof of one or any downstream consequence. Keyword checks alone would not
establish that fact: the proof roles above explain why the lower constructions
are independent of those conclusions.

## Complete structural import audit

The audit base is Library commit
`d54bbb9c881aa001e78c70a31a3a7bcb88affb43`.
All project imports were parsed recursively, stripping nested Lean
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

The code scan found no excluded declaration name and no
proof holes, new axioms or unsafe execution commands. The mathematical proof
audit above also checks the conclusions represented by those names. The
only textual exclusion hits in imported paired prose state restrictions:
`MirabolicMinus.md` denies use of square-integrable classification and generic
segment-product uniqueness; the target Markdown discusses its
highest-derivative consumer and minus exactness.
They are not proof inputs.

## Full independence boundary

The following full exclusion union is the audit boundary of this proof.
References to a consumer's proof also apply to every prerequisite, including
this theorem. This proof additionally excludes the
highest-derivative pairing consumer (BZ77 Proposition 3.8,
`MirabolicHighestDerivativePairingProof`) and any other proof of that proposition.
It neither uses nor duplicates minus exactness.


This is a BZ77-only upstream detection input for mirabolic strong indecomposability, ordered-socle existence and the nonadjacent two-supercuspidal product `TwoSupercuspidalNonadjacentProductIrreducible`. It does not duplicate or replace the combined Ze80 section 5.4 reduction statement. That combined reduction and its strong-indecomposability conclusion are not used to prove detection. Neither the nonadjacent product conclusion nor the full two-supercuspidal product-structure conclusion `TwoSupercuspidalProductStructure`, including its adjacent composition/Jacquet conjuncts, is used. The proof route is general BZ77 derivative theory and independent of these consumers.

The conditions of the nonadjacent product allow a fully proved BZ77 derivative route and forbid using Ze80 segment derivative formulas or circular results. Every lower derivative result used has a published proof. A citation, unproved proposition or draft is not a proof input. The following full union of exclusion sets holds, including mathematical conclusions, the modules that prove them and transitive dependencies, for all later proofs and lower prerequisites.

Conclusions, proofs and transitive proof dependencies of ordered-socle existence, socle exhaustion, analytic segment classification, unlinked segment-socle product irreducibility, the final segment-socle irreducibility criterion, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, the special-head product irreducibility criterion, special-head exhaustion, ordered special-head existence, quotient coverage, tempered block uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable exhaustion, regular exhaustion, `GenericSegmentProductUniqueness`, ordered special-segment conversion and forward special-segment essential square-integrability are not used. This full exclusion set holds for later proofs and lower prerequisites. Shared lower inputs need their own independence audit.

Additional exclusions for the nonadjacent product (they concern that product and every prerequisite, including detection):

Neither that
proof nor any prerequisite depends directly or transitively on the following
results, their mathematical conclusions, the modules that prove them or downstream
consequences:

- Individual special-head/reverse-socle existence.
- Individual segment-socle/reverse-head existence.
- Analytic segment classification.
- Forward special square-integrability,
  `SegmentSpecialEssentialSquareIntegrability`.
- Multisegment special-head exhaustion.
- Ordered strong-head existence.
- Quotient coverage.
- Ordered conversion.
- Tempered uniqueness.
- `SquareIntegrableLanglandsClassification`.
- Square-integrable exhaustion.
- Regular exhaustion.
- Special-head product irreducibility.
- `GenericSegmentProductUniqueness`.
- `OrderedMultisegmentSocleExistence`.
- `MultisegmentSocleExhaustion`.
- `SegmentSocleProductIrreducibility`.
- Adjacent socle commutation.
- `SegmentFullJacquetFormula`, its statement and its proof (`segmentFullJacquetFormula`
  in `Classification.SegmentFullJacquetProof`).
- `SegmentHeadJacquetFormula`.
- `SegmentSocleJacquetFormula`.
- `SegmentSpecialJacquetExponentNormFormula`.

The full-formula results add these restrictions: Ze80's segment derivative
formulas (§3.5 or §9.6) are not used, and no derivative result (including
BZ77's) is assumed without a published proof; no segment product
irreducibility criterion (Ze80 4.2 or 9.7), analytic or
square-integrability result (Ze80 9.3), or classification or exhaustion
theorem is assumed. Ze80 Theorem 4.2's linked-pair converse rests on §2 and cannot
prove Proposition 1.11 circularly. These exclusions hold unweakened for every
prerequisite, and the import and mathematical proof-dependency audit is
documented in the final proof Markdown. Shared lower constructions are reused
only after their independence is checked.

The full transitive project import closure is audited against the public Library and recorded completely in the paired Markdown. Ze80 section 3.5 or 9.6 and the segment-socle statements of `Classification.SegmentSocleDerivativesStatement` are not used; this detection assertion requires no segment or cuspidal derivative formula at all. Shared lower constructions are reused only after independence checks.

This full exclusion union holds unweakened for every lower prerequisite of this proof.


## Validation

The environment is Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The proof adds only its own pair. All existing Library pairs, including
the target and its entire dependency closure, remain unchanged.

A development check compiled the final
proof and a private declaration-inspection module with zero errors and zero
warnings. The complete unapplied type printed as

```lean
∀ {p : ℕ} [Fact (Nat.Prime p)] (F : PadicField.{uF} p)
  (T : F.TopologicalData), MirabolicOneStepDetection.{uF,uV} F T
```

The inspection reports independent level parameters `uF`, `uV` and exactly
`propext`, `Classical.choice`, `Quot.sound`. The private diagnostic
module is not part of the Library. A full hash comparison also found all
11,712 pre-existing public-base files unchanged.
