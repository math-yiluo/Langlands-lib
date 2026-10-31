# Positive derivative detection for every smooth mirabolic representation

Author: Worker 658.

The theorem `Langlands.Derivative.mirabolicDerivativeDetection` proves exactly
`Langlands.Derivative.MirabolicDerivativeDetection.{uF,uV} F T`, with outer
parameters `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`. It applies the already published theorem
`Langlands.Derivative.Mirabolic.derivativeDetection F T` from
`Langlands.Representation.Derivative.MirabolicDerivativeVanishing`.
Only this new Lean/Markdown pair is contributed. The imported proofs are reused
by their Lean names and are not resubmitted or claimed as new work.

## Exact scope

The proposition installs the supplied `T.topology`, then quantifies every
continuous nontrivial unitary additive character `ψ`, every `N : ℕ`, and every
actual `SmoothRep.{0,uF,uV} ℂ (GeneralLinear.mirabolic N F.Carrier)`. It says
`Nontrivial A → 0 < level T ψ A`. The group here is BZ77's `P_(N+1)`;
`Nontrivial` means that the representation's actual carrier is nontrivial.
The universes of the field and representation space remain independent.
There is no length, admissibility, irreducibility, homogeneity or exactness
hypothesis. The field, topology, minus functors, rank transports, derivative
orders and level are the existing Library constructions, unchanged.

The level is the bounded `Nat.findGreatest` of the orders
`0 < k ∧ k ≤ N+1` for which the actual
`mirabolicDerivativeOfOrder T ψ N k hk` has a nontrivial carrier, with default
zero. Its target is `GL_(N+1-k)`. For `N = 0`, the only order is one, and the
existing order-one identity identifies it with `Mirabolic.psiMinus T 0`,
with target `GL_0`. No order-zero derivative is introduced.

## Original source and implemented argument

The registered original is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The relevant passages were read in the original: Proposition 3.2(e), printed
p. 451 (one-based PDF page 12), and §3.5, printed p. 452 (PDF page 13).
The original is available from [Numdam](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0/)
and the [author's publication copy](https://www.math.tau.ac.il/~bernstei/Publication_list/publication_texts/BZ-induced-1.pdf).
Checks of the project errata material and these source records, supplemented by
bounded searches for corrections, found no applicable correction to these
passages; this is not a claim that every possible erratum was located.

Proposition 3.2(e) gives the sequence
`0 → Φ⁺Φ⁻ → Id → Ψ⁺Ψ⁻ → 0`. Section 3.5 defines
`τ^(k) = Ψ⁻(Φ⁻)^(k-1)(τ)` and constructs a finite filtration with layers
`(Φ⁺)^(k-1)Ψ⁺(τ^(k))`. The source concludes that vanishing of all derivatives
forces vanishing of the representation. The implemented argument proves this
consequence directly, without constructing the filtration or using the plus
functors or their exact sequence. The wrapper applies the following published
proof chain.

1. **The `P_1` boundary.** In `MirabolicDerivativeVanishing`,
   `radical_acts_trivially_zero` uses the subsingleton radical at rank zero.
   `relations_one_eq_bot` makes all trivial-character relation generators zero.
   Consequently `subsingleton_of_psiMinus_zero` uses `Jacquet.Localization.mk_eq_iff`
   to show that equality in the coinvariant quotient is equality of vectors.
   A subsingleton `Ψ⁻ A` therefore forces a subsingleton `A`.
2. **One step at positive rank.** The proved theorem
   `Mirabolic.subsingleton_of_psiMinus_phiMinus` in `MinusVanishing` says that
   for `A` on `P_(m+2)`, subsingleton carriers of `Ψ⁻ A` and `Φ⁻ A` force a
   subsingleton carrier of `A`. Its proof is described and audited below.
3. **Descending rank induction.**
   `subsingleton_of_forall_mirabolicDerivative` inducts on `M` for a
   representation of `P_(M+1)`, assuming vanishing for every splitting
   `M = n+j`. At `M = m+1`, the derivative with `(n,j)=(m+1,0)` is `Ψ⁻ A`.
   Every derivative of `Φ⁻ A` is one of `A`'s derivatives: after substituting
   `m = n+j`, the equality is definitional because `phiMinusIterate` applies
   the largest-rank `Φ⁻` first. The induction hypothesis kills `Φ⁻ A`, and
   the positive-rank one-step theorem kills `A`.
4. **Orders and level.**
   `subsingleton_rankCast_mirabolicDerivative_congr` transports vanishing
   between equal ranks and iteration counts by substitution.
   `subsingleton_of_forall_mirabolicDerivativeOfOrder` takes order `k=j+1`
   and uses `N+1-(j+1)=n` to apply the preceding induction. Finally
   `derivativeDetection` uses `level_eq_zero_iff`: level zero makes every
   positive-order derivative subsingleton, hence makes `A` subsingleton,
   contradicting `Nontrivial A`. Otherwise the natural-number level is positive.

The determinant inverse-half twists affect the actions but preserve the
coinvariant quotient carriers. The proof uses only those carriers, so it needs
no determinant/Haar-modulus identification. It does not use the conditional
`MirabolicDerivativeOrderBridge` draft or a pending rank-one or one-step proof.

## Mathematical dependency and provenance audit

The audit was performed for task `ed056880-a4dc-4ebf-ad26-9878e508cf6c`,
revision 3, including all its Independence exclusions and the complete trusted
operator conditions in correspondence `bd71b9185aab5d6eafffb7891bd3a3ca`.
All 150 imported Lean/Markdown files are byte-identical to the public Library
at both `b1b14ab0a6b31c85e9a1c5fd41cc248c2d4f0dce` and
`ddcb24bcc9c4fe817800414f5fd5f3536da42760`. No imported pair is edited.
The unchanged detection statement has Lean SHA256
`41824396183c6ad18890a7c51ec5f3c0cd1a0c1b66803c4078f85fcf32d038ab`
and Markdown SHA256
`b8540cb2f3b19c71308e6f66fbe3bc0a2096f68b74cab7015d76cf51f16771d2`.
Its statement publication is candidate `9e5f2dd4-a832-40da-9eaa-ad6e86064d29`,
Reviewer 4853, commit `d3985dbb10c55a703b1ca560439739837d09e8a6`;
that publication itself is not a proof input.

The substantive shared helper proofs were checked in the current source and
against their accepted publication records and independent semantic reviews.
The following table identifies their provenance. An artifact which introduced
a helper inside a larger proof supplies provenance for that helper; it does
not create an import of the other files in that submission.

| Current helper | Independently accepted publication | Use and checked correspondence |
| --- | --- | --- |
| `MirabolicDerivativeVanishing` | `f957ae76-3779-4436-bdcb-98bc63561e07`, Workers 1024 and 805, Reviewer 4988; commit `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11` | Current pair is byte-identical. Supplies the boundary, induction, order transport and detection theorem. The other highest-derivative/pairing files in its submission are not imported. |
| `MinusVanishing` | `c6026915-8731-45a8-bd21-ef1ac39654b8`, Worker 1025, Reviewer 4480; commit `771cfc69d1ff795522e29cdead1b7c40f1a1c308` | Current pair is byte-identical. This `lean.definition` publication includes the fully proved, independently reviewed one-step theorem, rather than a conditional statement. |
| `MirabolicLatticeBox` | `18329839-964e-4149-951b-fb99bda576c6`, Reviewer 3712; commit `83bd84354679646bd127657889be51d0b580ed3b` | The helper is authored by Worker 806; its Lean is byte-identical to the helper in this independently reviewed minimality-proof publication. The minimality theorem is not imported. Supplies compact open boxes, duality and character sums. |
| `Jacquet.CharacterAveraging` | `faa65dca-289a-4fb5-941a-b5e1200ff62e`, Reviewer 4000; commit `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` | Current code only extracts its duplicate orbit-translation proof to `Compact.OrbitMeanTranslation` and adjusts that call's arguments. The generic averaging proofs otherwise agree. No two-block deformation assembly from that submission is imported. |
| `Compact.orbitMean_apply` in `Compact.OrbitMeanTranslation` | `a5d47bfd-84ef-4d9b-8745-517947398a54`, Reviewer 638; commit `e3c2fa98be720f63c6981efbbdf15cd223329e76` | Extracted theorem block is byte-identical to its accepted `Jacquet.ExactProof` origin. It proves invariance of a finite orbit mean under translation. The full Jacquet exactness theorem is not imported. |
| `isCompact_additiveLattice`, `isOpen_additiveLattice` in `PadicLatticeTopology`, and `mem_additiveLattice_of_forall_mul_eq_one` in `ZeroRowLastRowCutoffProof` | `c1ca32b0-5a13-4540-95ca-4b21576ff387`, Worker 252, Reviewer 3434; commit `6d91111e6f9b7a27124b1de32a4984bbdd222a61` | The two extracted topology proof blocks are byte-identical to the accepted cutoff-proof origin. The remaining cutoff module only adds that import and deletes those moved blocks. The scalar annihilator proof is unchanged. |
| `PadicAdditiveConductorProof` | `8f35e474-ea64-4213-b49c-80f70e559886`, Reviewer 2908; commit `6543e70ef8c82ed8535a0f9fd06c59ed896bc738` | Current pair is byte-identical. Supplies actual valuation-lattice transport, integer-ring factorization and integer-ring annihilator lemmas. |
| Integer-ring topology helpers in `PadicScalarHaarScalingProof` | `391187ae-1d4c-4be0-804e-2fe896a2d21e`, Worker 90, Reviewer 618; commit `01a58491bc71539f1ecd3d5f0eec6ab8eae20fed` | The compactness/openness proofs are unchanged. Current code adds `LocalField.Topology`, removes its duplicate Hausdorff certificate and uses the existing `fieldT2`. The scalar Haar-scaling theorem is not used by the detection argument. |

For the one-step theorem, the mathematical route was checked beyond its
statement. Subsingleton coinvariant quotients make the trivial and `θ_ψ`
relation spaces all of the representation. Elementary Levi conjugation and
an invertible matrix with prescribed nonzero last row transport the latter
to every nonzero coordinate character; the trivial quotient covers the zero
character. `eventually_characterAverage_eq_zero` kills each vector's average
at some radical-box level for each coordinate character. Local constancy and
compactness of a parameter box yield a single level for all its characters.
Smoothness supplies a smaller box fixing the vector. Finite Fourier
orthogonality on the two finite box quotients then kills the vector itself.
Finiteness here concerns compact/open subgroup quotients, with no finiteness
restriction on the representation space.

The shared lattice-box proofs use the actual supplied valuation lattices,
compactness/openness of the integer ring, the actual character conductor and
the scalar annihilator lemma. Their use of `ZeroRowLastRowCutoffProof` is
restricted to these arithmetic facts. Its remaining Rankin–Selberg branch
imports last-row topology, Whittaker-function and quotient-integral definitions
and elementary matrix identities. No convergence, factor-existence,
functional-equation or classification result enters the detection proof.
The complete branch was included in the import scan below, even where its
mathematics is unused by this theorem.

`CharacterAveraging` constructs algebraic finite orbit means for a smooth
action restricted to a compact open subgroup and a character with open
kernel. Translation permutes a finite orbit; the relation-space and
exhaustion arguments follow by linearity and finite spans. Its functional
extension results are also proved generic linear algebra, not segment or
classification assertions. `Group.GL.Padic` supplies the group topology,
continuity and local compactness from the field's supplied topology and
finite-dimensional p-adic topology. Its optional canonical-topology aliases
are not used to replace `T`. The remaining construction layer consists of
matrix groups, rank maps, characters, smooth representations, quotient and
subquotient carriers, twists, compact means, and field normalization. A
statement module in this layer defines a proposition; no such proposition
is assumed as a theorem. The proof uses the corresponding proved lemmas or
the definitions themselves.

## Complete project import closure

The new module has one direct import, `MirabolicDerivativeVanishing`. There
are exactly 75 distinct transitive `Langlands` imports (76 modules including
this new wrapper). The protected detection-statement closure contains 54
modules. The complete list below includes all branches, not just mathematical
proof dependencies. Each module's imports were followed recursively and its
Lean and paired Markdown scanned against the full excluded names and task
IDs. Relevant helper declarations and their proofs were then inspected as
described above; absence of a name alone was not used to establish provenance.

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
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement
Langlands.Representation.Derivative.MirabolicDerivativeVanishing
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
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

The scan found no excluded reference in a Lean proof or import. The broad
word “exhaustion” occurs in the generic compact-open subgroup exhaustion in
`CharacterAveraging`; it has no connection with representation-classification
exhaustion. Markdown hits are scope/independence explanations or references
to downstream uses: for example `LocalField.Topology` mentions classification
as a consumer and `Category.Twist` mentions a downstream determinant-twist
application. None is an import or proof premise.

## Full exclusion audit

The proof and every imported prerequisite are independent of the following
conclusions, their proof successors and their downstream consequences. Task
IDs below identify the checked prohibition, not an input.

- The consumer reduction `MirabolicStrongIndecomposabilityReduction` and its
  conclusion; strong indecomposability task
  `ff4738d8-47e3-433b-bedc-629bc2d492a7`; the nonadjacent product conclusion
  `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`; and the full two-supercuspidal product
  structure, including adjacent composition and Jacquet clauses,
  `ab61f565-1427-4746-ba77-46097563e962`.
- Ordered-socle existence `23189526-80b0-4828-a6d4-7ebec2cbeef5`, socle
  exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`, analytic segment
  classification `aca8805b-054f-4d56-8045-12db7f623404`, unlinked segment-socle
  product irreducibility `23e98d90-6055-4e35-91a9-b0f5d8a84961`, final
  segment-socle irreducibility `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`,
  `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, and
  adjacent socle commutation `e3634665-571b-4852-9f4c-bab8a1053434`.
- Special-head product irreducibility `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`,
  special-head exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered
  special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient
  coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness
  `52e97845-36bb-457d-b76f-70753334b88c`,
  `SquareIntegrableLanglandsClassification` /
  `1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion
  `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, regular exhaustion
  `bf433f0a-921a-428c-b0c0-6475438125ac`,
  `GenericSegmentProductUniqueness` / `30341ae4-65f2-4a0e-9283-763db01a409e`,
  ordered special-segment conversion `8252833d-c269-41a9-824c-5879e531b23b`,
  and forward special-segment essential square-integrability
  `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`.
- Individual special-head/reverse-socle existence
  `67279e36-f3c2-42e3-9302-11729784042e`, individual
  segment-socle/reverse-head existence `4ca79bbd-589e-476b-9f65-661e799984b5`,
  `SegmentSpecialEssentialSquareIntegrability`,
  `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`, and
  `SegmentSocleProductIrreducibility`.
- `SegmentFullJacquetFormula`, its statement/successor-arrangement task
  `ed48ae06-964c-4c84-9e62-978f5a953ca7` and exact proof successor;
  `SegmentHeadJacquetFormula` / `55ad1e10-62d8-46b7-a081-909ef0056426`;
  `SegmentSocleJacquetFormula` / `b95105c6-f8bb-4641-ae53-2f49d1e7f034`;
  and `SegmentSpecialJacquetExponentNormFormula` /
  `92aea10f-62ac-4e0b-bd4a-9a80909797c5`.
- Ze80's segment derivative formulas (§3.5 or §9.6), its product irreducibility
  criteria (4.2 or 9.7), its analytic/square-integrability result (9.3), all
  classification or exhaustion theorems, and the segment-socle part of
  `8e5b4563-0365-41c7-b134-70f2a0b36292`.

None of these appears as a mathematical dependency in the proof chain above.
No segment or cuspidal derivative formula is needed. The operator-paused
minus exactness task `b65bc667-6951-4bd5-82af-10fb7046df7f` is neither used,
duplicated nor requested for resumption. The proof requires no new premise,
plus model, exactness theorem, filtration, Haar-modulus bridge, product,
head, socle or classification result. No lower task was split off.
