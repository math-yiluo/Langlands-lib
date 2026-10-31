# The terminal mirabolic full upper quotient

Author: Worker 1004.

This internal construction identifies the full upper-unipotent character
quotient on the actual rank-one mirabolic group with the published normalized
`Ψ⁻` functor. Its final constructor is
`Langlands.Derivative.TopLocalization.mirabolicZeroIso`:

```text
mirabolicUpperCoinvariantsFunctor ψ 0 ≅ Mirabolic.psiMinus T 0.
```

The parameters are `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p`, `T : F.TopologicalData`, and an arbitrary raw
additive character `ψ : AddChar F.Carrier ℂ`. The functor type installs
`letI := T.topology`. Its source category is
`SmoothRep.{0,uF,uV} ℂ (mirabolic 0 F.Carrier)` and its target category is
`SmoothRep.{0,uF,uV} ℂ (GeneralLinear 0 F.Carrier)`. The field and module
universes are independent. Both whole quotient carriers in `Type uV` are
retained, including every possible multiplicity of a `GL₀` representation.
No continuity, unitarity or nontriviality is required of this raw character,
and there are no finite-length, admissibility, irreducibility, genericity,
nonzero-object or dimension premises.

Here `mirabolic 0` is `P₁`, not `GL₀`. This is the terminal step needed after
all the positive mirabolic minus steps. Higher-rank iteration, the ordinary
rank casts, the all-rank top-localization adapter and the exact exterior-tensor
theorem are separate obligations.

## Provenance and original conventions

The convention source is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, original PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original was read at §1.8(b), printed pp.444–445 / PDF pp.5–6,
and §3.1, printed p.450 / PDF p.11. The former supplies the actual quotient
by the span of `π(u)v - θ(u)v`, with the negative inverse-half normalization
on the remaining action. The latter supplies the last-row mirabolic and
last-column radical conventions. The rank-one extension and explicit
natural isomorphism here are internal consequences of the published matrix
and quotient definitions, not an assumed derivative comparison from the
source. No source-specific errata note was found in the supplied project and
Library notes and literature index in the earlier bounded source check.

The source does not serve as an unproved Lean transitivity input. The only
quotient equivalence used here is the independently published
`Jacquet.Localization.transportEquiv`. The target functor is exactly the
existing `Mirabolic.psiMinus T 0`, including its determinant inverse-half
twist. No identification of this explicit twist with a Haar modulus is
asserted or needed.

## Implemented equivalence and naturality

The published `Mirabolic.rankOne_eq_one` proves that the sole matrix entry
of any element of `P₁` equals one, using its defining last-row equation.
`Mirabolic.rankOneSubsingleton` records that every element is the identity.
Consequently any two subgroups of `P₁` agree.
`mirabolicZero_upper_eq_radical` applies this fact to the actual
`Mirabolic.upperUnipotent 0 F.Carrier` and `Mirabolic.radical 0 F.Carrier`.
This does not replace either subgroup by an abstract group.

`mirabolicZeroEquiv T ψ A` applies `Localization.transportEquiv` to the same
representation `A.representation`, the actual upper and radical subgroups,
`MulEquiv.subgroupCongr mirabolicZero_upper_eq_radical`, and the identity
coefficient linear equivalence. Restricted-action compatibility is reflexive.
For character compatibility, each upper-group element is one, so both the
published `mirabolicUpperCharacter ψ 0` and the trivial radical character
have value one by their homomorphism identity laws. This works even for the
zero additive character.

The transport's forward and backward quotient lifts are thus well-defined
on the actual relation spans. Its published proof checks both composites
using quotient hom extensionality and the inverse coefficient maps. The
resulting `LinearEquiv` is packaged as a representation equivalence to the
actual normalized `psiMinus` object. Equivariance uses the fact that every
`g : GeneralLinear 0 F.Carrier` is one (empty matrix coordinates), then the
representation identity law on each side. In particular the normalization
has not been discarded: its value at the identity is one within the actual
normalized representation.

The two representative formulas are proved by reflexivity as
`mirabolicZeroEquiv_mk` and `mirabolicZeroEquiv_symm_mk`:

```text
[v]_(upper,ψ)  ↦  Mirabolic.psiMinusQuotient T 0 A v,
Mirabolic.psiMinusQuotient T 0 A v  ↦  [v]_(upper,ψ).
```

The entire quotient modules, rather than selected vectors or dimensions,
are related by these inverse maps. `mirabolicZeroIso` applies
`SmoothRep.mkIso` to each component and `NatIso.ofComponents` to assemble
them. For any smooth `P₁` intertwiner `f`, each naturality composite sends
the original class of `v` to the radical class of `f(v)`. The proof reduces
through smooth/representation hom extensionality and then
`Localization.hom_ext` to this reflexive representative equality. The maps
of the existing normalized `psiMinus` still are the induced quotient maps;
twisting preserves their underlying linear maps. Inverse naturality follows
from the constructed natural isomorphism.

## Import and mathematical proof-dependency audit

The sole direct import is the independently accepted and published
`Derivative.TopLocalizationRestriction`. Its complete pair and the used
`Mirabolic`, `MirabolicMinus`, `Localization` and `LocalizationTransport`
constructions were inspected. No pending step candidate or private draft is
an input. The restriction module supplies the exact full upper functor and
character. Its GL-to-mirabolic restriction comparison is not used here.
`PartialDerivativeTensorLocalization` occurs transitively for that functor's
fixed dependencies; its tensor comparison theorem is unused.

The actual new proof inputs are the elementary rank-one matrix-coordinate
identity, subsingleton subgroup equality, homomorphism identity laws,
the two quotient lifts and inverse laws in `transportEquiv`, the unchanged
normalized `psiMinus` definitions and induced maps, trivial `GL₀` actions,
and the elementary natural-isomorphism constructors. No general derivative
comparison, representation-finiteness result or dimension computation is
assumed. The scalar-vanishing lemma in `LocalizationTransport` is unused.

Recursive traversal of the actual project imports gives exactly 66 modules,
listed below, excluding this entry module. All imported Lean/Markdown pairs
in the workspace agree byte for byte with current Library
`c6045fe1328899de3416096b16eb72db93a6c7fc`. The target
`PartialDerivativeTensorStatement` pair retains the exact contract hashes
`30c22587bab476fab8c6a190841b30c41f8dfa20b9f40b0187254c3f53227f41`
for Lean and
`e21ce266515ce4c853255f63bd98c8dd5bb097ded93fec62c9c329415b5e8c15`
for Markdown. Neither it nor any imported pair was edited here.

The historical restriction publication's smaller closure predates a published
elementary extension of `Group.GL.NormalizedCharacter` importing
`Topology.CompactNormCharacter`. That complete helper pair was inspected:
it imports Mathlib only, and its compact-character proof bounds powers and
inverses. The historical `RankinSelberg.LastRowReduction` namespace adds no
consumer import. Neither that theorem nor its proof is used here. The current
66-module closure is audited rather than treating the older closure as
unchanged.

The broad source scan finds arithmetic field/residue-degree finranks, generic
admissibility and finite-length predicates and elementary twist-preservation
lemmas, the unused Fourier `IsSelfDual` proposition, and the unused
`WhittakerPrerequisitesStatement` proposition. These do not supply any
representation-finiteness, representation-duality or excluded consumer
conclusion. The exact same full parent exclusions bind this terminal unit;
the following checks cover named conclusions, successors and transitive
consequences as well as the direct imports.

| Excluded family and parent task references | Terminal mirabolic proof audit |
| --- | --- |
| `SegmentHeadProductIrreducibility` (`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`); `GenericSegmentProductUniqueness` (`30341ae4-65f2-4a0e-9283-763db01a409e`); individual special-head/reverse-socle (`67279e36-f3c2-42e3-9302-11729784042e`) and segment-socle/reverse-head (`4ca79bbd-589e-476b-9f65-661e799984b5`) existence | No segment, head or socle module occurs. The inverse maps use only the existing quotient transport universal property. |
| Multisegment exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), ordered conversion (`8252833d-c269-41a9-824c-5879e531b23b`) | No multisegment, ordering or coverage theorem occurs. Both maps preserve the original quotient representatives. |
| Tempered uniqueness (`52e97845-36bb-457d-b76f-70753334b88c`), `SquareIntegrableLanglandsClassification` (`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable exhaustion (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`), regular exhaustion (`bf433f0a-921a-428c-b0c0-6475438125ac`), analytic segment classification (`aca8805b-054f-4d56-8045-12db7f623404`), `SegmentSpecialEssentialSquareIntegrability` (`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`) | No classification or square-integrability input occurs. Every original module carrier is arbitrary. |
| `UnlinkedSegmentSocleProductIrreducible` (`23e98d90-6055-4e35-91a9-b0f5d8a84961`), `LinkedSegmentSocleReverseProductStructure` (`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`), `LinkedSegmentSoclePairReducible` (`8fa9f68b-fa1b-431a-97f6-5b163964d1fc`), `SegmentSocleProductIrreducibility` (`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`), juxtaposed structure and quotient-Hom (`7ff2a1e9-89dc-439e-a861-a567b3db92bf`) | No socle, representation product-structure, reducibility or quotient-Hom theorem occurs. |
| Adjacent socle commutation (`e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`), two-segment commutation (`426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0`), linked gluing (`c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea`), `OrderedMultisegmentSocleExistence` (`23189526-80b0-4828-a6d4-7ebec2cbeef5`), socle exhaustion (`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`) | No socle commutation, gluing or exhaustion module or theorem occurs. |
| `SegmentFullJacquetFormula` (`ed48ae06-964c-4c84-9e62-978f5a953ca7`), `SegmentHeadJacquetFormula` (`55ad1e10-62d8-46b7-a081-909ef0056426`), `SegmentSocleJacquetFormula` (`b95105c6-f8bb-4641-ae53-2f49d1e7f034`), `SegmentSpecialJacquetExponentNormFormula` (`92aea10f-62ac-4e0b-bd4a-9a80909797c5`); all segment derivative formulas and parent six-statement parts (b), (d), (e), (f) | No segment formula is used. General localization supplies the relation quotient; the actual normalized psiMinus is retained at rank zero. |
| `TwoSupercuspidalNonadjacentProductIrreducible` (`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`), `TwoSupercuspidalProductStructure` (`ab61f565-1427-4746-ba77-46097563e962`); Ze80 §§3.5, 9.6, Theorems 4.2, 9.7 and 9.3 | No product criterion, segment derivative, analytic theorem or unproved BZ77 derivative result is used. No Haar bridge is needed. |
| `IrreducibleCoinvariantFinitenessStatement` (`5ab445dc-d2b4-4072-80d1-6370870a4a26`), `LeviCuspidalCoinvariantFinitenessStatement` (`3ff5c8fb-397c-4345-bcb3-5d98a0993d18`), the dependent mirabolic finite-length route (`5428fe2c-013c-482d-aa6e-7df43e7191aa`), `SupercuspidalCoinvariantFinitenessStatement` (`62de5903-b616-4b5c-88eb-a066b77c5467`) | No representation-finiteness input occurs. The imported finite-length predicate and arithmetic degrees described above are unused. |
| Proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` (`2e5183b1-01e9-44fb-b26c-f4521a25c7c7`) | No classification module occurs. Neither UpperUnipotentCharacterFactorization nor TopDerivativeCoinvariantComparison, whose closure reaches the excluded host, is imported. No derivative dimension is used. |
| Plus, adjunction, representation duality, derivative filtration, pairing, or unproved general derivative comparisons | No such theorem is used. The dual module only defines linear functionals. No tower comparison is used by this terminal unit. Higher-rank iteration and the all-rank adapter remain separate obligations. |

### Complete transitive project import list

The list includes the sole direct import and excludes this entry module.

```text
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
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.Partial
Langlands.Representation.Derivative.PartialDerivativeTensorLocalization
Langlands.Representation.Derivative.PartialDerivativeTensorStatement
Langlands.Representation.Derivative.TopLocalizationRestriction
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.OneFactor
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
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
