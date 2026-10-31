# Mirabolic restriction of full upper localization

Worker 1004 constructs a natural comparison between the actual full
upper-unipotent quotient of a `GL_(n+1)` representation and the same quotient
after restriction to the actual mirabolic subgroup `P_(n+1)`. This is internal
subgroup-copy infrastructure for the all-rank top-localization adapter.
Its final constructor is
`Langlands.Derivative.TopLocalization.upperRestrictionIso`:

```text
PartialTensor.upperCoinvariantsFunctor ψ (n + 1) ≅
  generalLinearRestriction T n ⋙ mirabolicUpperCoinvariantsFunctor ψ n.
```

Here `K : PadicField.{uF} p`, `T : K.TopologicalData`, and
`ψ : AddChar K.Carrier ℂ` is arbitrary. The type is formed after
`letI := T.topology`. The source category is
`SmoothRep.{0,uF,uV} ℂ (GeneralLinear (n + 1) K.Carrier)` and the target
category is `SmoothRep.{0,uF,uV} ℂ (GeneralLinear 0 K.Carrier)`.
Both sides keep the entire actual quotient carrier in `Type uV` with the
trivial `GL₀` action. The field and module universes remain independent.

The algebraic constructors work over every commutative coefficient ring
`F : Type uF`, for arbitrary complex modules, with no topology. The auxiliary
smooth functor requires only `TopologicalSpace F`. The final natural
isomorphism uses the exact published p-adic restriction functor, hence its
stated p-adic telescope. No unitarity, continuity or nontriviality hypothesis
is imposed on the additive character. All `n : ℕ` are allowed, including
`n = 0`, which compares the two actual rank-one quotients. The original
rank-zero `GL₀` case has no mirabolic restriction step and is outside this
constructor.

This unit does not prove quotient transitivity, a top-derivative comparison,
a determinant-twist identity or the exterior-tensor theorem. Those remain
separate obligations. No unpublished unit is imported.

## Provenance and original conventions

This is an internal application of the published
`Jacquet.Localization.transportEquiv`. Its hypotheses are discharged by the
identity coefficient map and the published actual unipotent subgroup
identification. It assumes neither a new quotient comparison nor a derivative
theorem.

The original convention source is Bernstein–Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`. The retained original PDF has SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The passages read for this construction are §1.8(b), printed p.444 / PDF p.5,
with the following discussion on printed p.445 / PDF p.6, and §3.1, printed
p.450 / PDF p.11. The first defines localization using the span of
`π(u)v - θ(u)v`; the latter defines the actual mirabolic subgroup by its
last row and explains restriction from `GL` to that subgroup.
Only those conventions are used. In particular, none of Proposition 1.9's
transitivity, adjunction or tensor assertions is an assumed proof input.
The extension to arbitrary commutative rings, explicit subgroup-copy maps
and natural isomorphism are internal constructions. Bounded checks of the
project and current Library errata-note locations and literature filenames
found no source-specific errata note; this is only a local search result.

## Implemented maps and proofs

For clarity, let `U_G = GeneralLinear.upperUnipotent (n + 1) F` and
`U_P = GeneralLinear.Mirabolic.upperUnipotent n F`. The latter is literally
the comap of `U_G` along the actual mirabolic inclusion. The published
`Mirabolic.upperUnipotentEquiv : U_P ≃* U_G` forgets the redundant mirabolic
membership certificate. Its inverse inserts that certificate using
`upperUnipotent_le_mirabolic`, without changing the matrix. The published
proof checks both composites definitionally. This uses no abstract group
replacement or arbitrary choice of an isomorphism.

`mirabolicUpperCharacter ψ n` is exactly the pullback of
`Whittaker.entrywiseCharacter ψ (n + 1)` along this equivalence. Thus each
matrix has precisely the same units-valued character on the two sides, with
no inversion or change of additive character.

For `ρ : Representation ℂ (GeneralLinear (n + 1) F) V`,
`upperRestrictionLinearEquiv ψ ρ` specializes `Localization.transportEquiv`
with subgroup equivalence `Mirabolic.upperUnipotentEquiv.symm` and coefficient
equivalence `LinearEquiv.refl ℂ V`. The restricted representation is literally
`ρ.comp (mirabolic n F).subtype`. Action compatibility and character
compatibility therefore hold definitionally. The forward map sends the
original class `[v]` to the class of the same `v` in the restricted quotient;
`upperRestrictionLinearEquiv_mk` proves this formula. Its inverse has the
same formula in the opposite direction, proved by
`upperRestrictionLinearEquiv_symm_mk`.

The inspected proof of `transportEquiv` constructs the forward and backward
maps using `Localization.lift`. Compatibility with each character relation
makes each lift well-defined. Quotient hom extensionality verifies both
composites on original representatives, using the two inverse coefficient
maps. Thus the inverse laws here are actual proved linear-equivalence laws,
not an assumed injectivity statement or a dimension argument.

`mirabolicUpperCoinvariantsFunctor ψ n` assigns this actual relation quotient
to each smooth mirabolic representation and equips the whole quotient with
the trivial `GL₀` action. Every vector is fixed by the top open subgroup,
which proves smoothness directly. Its action on an ambient smooth
intertwiner is the published `Localization.mapLinear` for the fixed actual
subgroup and character. Since the output actions are trivial, this induced
linear map is equivariant. Quotient hom extensionality verifies identity and
composition, with both equalities reducing to the same original linear map
on `[v]`.

`upperRestrictionIso` uses the exact
`generalLinearRestriction T n`, the published continuous pullback along the
actual mirabolic inclusion. It retains both the original module and the
underlying morphisms. Each component is `SmoothRep.mkIso` applied to the
linear equivalence above, with the two trivial `GL₀` actions. Equivariance
is definitional. For every original smooth intertwiner `f`, both naturality
composites send `[v]` to `[f(v)]`. The implemented naturality proof uses the
actual quotient hom extensionality law and this representative calculation.
The inverse components and their naturality are supplied by the constructed
natural isomorphism. The quotient carrier is neither shrunk nor replaced by
a scalar multiplicity. No representation-finiteness assumption occurs.

## Import and mathematical proof-dependency audit

The two direct imports are the published
`Langlands.Representation.Derivative.PartialDerivativeTensorLocalization`
and `Langlands.Representation.Jacquet.LocalizationTransport`. The former is
used only for `PartialTensor.upperCoinvariantsFunctor`; none of its tensor
comparison theorems is used. The latter supplies the actual quotient
transport construction. Both complete Lean/Markdown pairs were inspected.
The new proof also uses the unchanged `Mirabolic` subgroup pair,
`Localization` quotient laws, `generalLinearRestriction`, the trivial
representation and elementary natural-isomorphism constructors.

Recursive traversal of the actual project import declarations gives exactly
64 modules, listed below, excluding this entry module. All 64 Lean/Markdown
pairs are byte-identical to workspace base Library
`7d8c1355c088b76a992b0af1690748d5ae7147b5` and inspected current Library
`7290311ebd03e23d11ae093f6e66366b39cf85f5`. The published target statement
pair and its entire dependency closure are unchanged. No private draft,
staged artifact or unpublished comparison enters this closure.

The actual mathematical inputs are the quotient lifts and hom
extensionality in `Localization`, the two explicitly inverse maps in
`LocalizationTransport.transportEquiv`, the actual subgroup-copy equivalence
in `Mirabolic`, the published entrywise-character definition, and the
continuous pullback defining ordinary restriction. Their inspected proof
bodies consist of quotient universal properties, subgroup certificates and
definitional formulas. The source action of the quotient transport is
literally the restriction of the original action, so no normalizer,
semidirect-product, localization-tower or normalization theorem is required.

The remaining imports come from the unchanged target's existing definitions
and the tensor helper's fixed closure. The broad source scan found only
arithmetic field/residue-degree finranks, the unused
`Category.Basic.HasFiniteLength` predicate and the unused Fourier
`HarmonicAnalysis.IsSelfDual` proposition in the excluded mathematical
families. These are not representation-finiteness or representation-duality
proof inputs. `LocalizationTransport` also contains an elementary scalar
vanishing criterion; it is unused by this construction.

Every exclusion of the parent task remains binding. Each following row
checks both the actual import closure and the implemented mathematical proof
inputs, including the named conclusions, proof successors and downstream
consequences.

| Excluded family and parent task references | Restriction proof audit |
| --- | --- |
| `SegmentHeadProductIrreducibility` (`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`); `GenericSegmentProductUniqueness` (`30341ae4-65f2-4a0e-9283-763db01a409e`); individual special-head/reverse-socle (`67279e36-f3c2-42e3-9302-11729784042e`) and segment-socle/reverse-head (`4ca79bbd-589e-476b-9f65-661e799984b5`) existence | No segment, head or socle module occurs. The inverse maps use only the existing quotient transport universal property. |
| Multisegment exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), ordered conversion (`8252833d-c269-41a9-824c-5879e531b23b`) | No multisegment, ordering or coverage theorem occurs. Both maps preserve the original quotient representatives. |
| Tempered uniqueness (`52e97845-36bb-457d-b76f-70753334b88c`), `SquareIntegrableLanglandsClassification` (`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable exhaustion (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`), regular exhaustion (`bf433f0a-921a-428c-b0c0-6475438125ac`), analytic segment classification (`aca8805b-054f-4d56-8045-12db7f623404`), `SegmentSpecialEssentialSquareIntegrability` (`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`) | No classification or square-integrability input occurs. Every original module carrier is arbitrary. |
| `UnlinkedSegmentSocleProductIrreducible` (`23e98d90-6055-4e35-91a9-b0f5d8a84961`), `LinkedSegmentSocleReverseProductStructure` (`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`), `LinkedSegmentSoclePairReducible` (`8fa9f68b-fa1b-431a-97f6-5b163964d1fc`), `SegmentSocleProductIrreducibility` (`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`), juxtaposed structure and quotient-Hom (`7ff2a1e9-89dc-439e-a861-a567b3db92bf`) | No socle, representation product-structure, reducibility or quotient-Hom theorem occurs. |
| Adjacent socle commutation (`e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`), two-segment commutation (`426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0`), linked gluing (`c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea`), `OrderedMultisegmentSocleExistence` (`23189526-80b0-4828-a6d4-7ebec2cbeef5`), socle exhaustion (`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`) | No socle commutation, gluing or exhaustion module or theorem occurs. |
| `SegmentFullJacquetFormula` (`ed48ae06-964c-4c84-9e62-978f5a953ca7`), `SegmentHeadJacquetFormula` (`55ad1e10-62d8-46b7-a081-909ef0056426`), `SegmentSocleJacquetFormula` (`b95105c6-f8bb-4641-ae53-2f49d1e7f034`), `SegmentSpecialJacquetExponentNormFormula` (`92aea10f-62ac-4e0b-bd4a-9a80909797c5`); all segment derivative formulas and parent six-statement parts (b), (d), (e), (f) | No segment formula is used. General localization supplies the relation quotient, and ordinary restriction is its exact published definition. |
| `TwoSupercuspidalNonadjacentProductIrreducible` (`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`), `TwoSupercuspidalProductStructure` (`ab61f565-1427-4746-ba77-46097563e962`); Ze80 §§3.5, 9.6, Theorems 4.2, 9.7 and 9.3 | No product criterion, segment derivative, analytic theorem or unproved BZ77 derivative result is used. No Haar bridge is needed. |
| `IrreducibleCoinvariantFinitenessStatement` (`5ab445dc-d2b4-4072-80d1-6370870a4a26`), `LeviCuspidalCoinvariantFinitenessStatement` (`3ff5c8fb-397c-4345-bcb3-5d98a0993d18`), the dependent mirabolic finite-length route (`5428fe2c-013c-482d-aa6e-7df43e7191aa`), `SupercuspidalCoinvariantFinitenessStatement` (`62de5903-b616-4b5c-88eb-a066b77c5467`) | No representation-finiteness input occurs. The imported finite-length predicate and arithmetic degrees described above are unused. |
| Proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` (`2e5183b1-01e9-44fb-b26c-f4521a25c7c7`) | No classification module occurs. Neither UpperUnipotentCharacterFactorization nor TopDerivativeCoinvariantComparison, whose closure reaches the excluded host, is imported. No derivative dimension is used. |
| Plus, adjunction, representation duality, derivative filtration, pairing, or unproved general derivative comparisons | No such theorem is used. The dual module only defines linear functionals. The generic quotient tower and higher-rank top-localization comparison remain open. |

### Complete transitive project import list

The list includes both direct imports and excludes this new entry module.

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
Langlands.Topology.Nonarchimedean.Subgroup
```
