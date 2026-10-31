# Rank-zero and rank-one top-localization comparisons

Worker 1004 constructs the natural comparison between the actual full
upper-unipotent character quotient and the published normalized top derivative
in ranks zero and one. This is internal boundary infrastructure for the
all-rank comparison. It retains arbitrary smooth module carriers in the
independent universe `uV`, with the actual supplied topology.

The exact outputs are `TopLocalization.topLocalizationZeroIso` and
`TopLocalization.topLocalizationOneIso` in namespace `Langlands.Derivative`.
For `m = 0` and `m = 1`, respectively, they have type

```text
PartialTensor.upperCoinvariantsFunctor ψ.complex m ≅ topDerivative T ψ m.
```

Here `F : PadicField.{uF} p`, `T : F.TopologicalData`, and `ψ` is the same
bundled unitary additive character on both sides. The construction keeps
`SmoothRep.{0,uF,uV} ℂ _` and the original `Type uV` carriers. It proves these
two boundaries only. The positive-rank quotient tower and the exact all-rank
exterior-tensor theorem remain separate obligations.

## Provenance and original conventions

This is an internal consequence of the published relation quotient and minus
functor definitions, rather than an assumed instance of a derivative theorem.
The original source is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, original PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The source passages used for conventions are:

- §1.8(b), printed p.444 / PDF p.5, and the following trivial-subgroup
  observation on printed p.445 / PDF p.6: the localizing space is the actual
  span of `π(u)v - θ(u)v`, its carrier is the quotient, and localization at the
  identity subgroup reduces to restriction.
- §3.5 and footnote 2, printed p.452 / PDF p.13: the mirabolic derivative is
  the indicated sequence of minus functors; the first derivative applies
  `Ψ⁻` with no preceding `Φ⁻`.
- §4.3, printed p.454 / PDF p.15: the zeroth ordinary derivative retains the
  original representation, and positive ordinary derivatives follow
  restriction to the mirabolic group.

The Lean normalization is exactly the existing determinant inverse-half twist
in `Mirabolic.psiMinus`. This unit makes no Haar-modulus identification.
The rank-zero extension and explicit quotient equivalences are internal
constructions. No filtration, pairing, cuspidal, classification or dimension
conclusion on these or neighboring pages is used. Bounded checks of the
project and current Library errata-note locations and literature filenames
found no source-specific errata note; this records the local check only.

## Implemented maps and proofs

The private lemma `singleton_relations` takes a group representation, a
subgroup `U`, an arbitrary units-valued character and a proof that every
`u : U` equals its identity. Each generator of `Localization.relations` is
then zero by the two homomorphism identity laws. Span minimality proves that
the whole relation submodule is bottom. The private
`singletonQuotientEquiv` applies Mathlib's `Submodule.quotEquivOfEqBot`.
Its maps are `[v] ↦ v` and `v ↦ [v]`; Mathlib constructs these as the lift of
the identity and the actual quotient map, with both composites verified.

At rank zero `GL₀` is a singleton group (empty matrix coordinates), so its
upper-unipotent subgroup is a singleton as well. `upperZeroEquiv` applies
the preceding linear equivalence to the actual full upper quotient. The
source action is the published trivial `GL₀` action from
`PartialTensor.upperCoinvariantsFunctor`; the target is the original
representation, whose action is the identity because every group element
is its identity. Equivariance follows by evaluating these linear maps.
`upperZeroEquiv_mk` records the formula on original representatives.
`upperCoinvariantsZeroIso` bundles these components naturally for arbitrary
smooth intertwiners. Its naturality proof uses quotient hom extensionality;
each composite sends `[v]` to the original intertwiner applied to `v`.

At rank one the private lemma `upperOne_eq_one` includes the actual `U₁`
in `P₁` using `upperUnipotent_le_mirabolic`, then applies the published
`Mirabolic.rankOne_eq_one` and removes the subgroup certificate. That
published proof uses the last-row defining equation of a one-by-one matrix.
The radical defining `Ψ⁻` at this rank is a subgroup of `P₁`, hence is also
a singleton by `Mirabolic.rankOneSubsingleton`.

`upperOneEquiv` composes the equivalence from the actual `U₁` quotient to
the original module with the inverse equivalence for the actual radical
quotient of the restricted representation. Thus it sends the original
upper-quotient class of `v` to `Mirabolic.psiMinusQuotient T 0 _ v`;
`upperOneEquiv_mk` verifies this formula definitionally. Its inverse sends
the latter class to the former. Restriction and twisting preserve module
carriers and the underlying linear maps. The target representation is the
actual normalized `psiMinus`, with its determinant twist still present.
Both acting groups are `GL₀`, so equivariance follows by evaluating at the
identity, including the normalization character's identity law.
`upperCoinvariantsOneIso` uses the same quotient-extensionality argument
for naturality in every original `GL₁` intertwiner.

`topDerivative_one` unfolds the exact published `topDerivative_eq`, uses
`generalLinearDerivative_one_one`, and reduces the remaining reflexive
rank cast and identity composition. The two final boundary isomorphisms
compose the preceding natural comparisons with the inverse of `eqToIso`
for this equation or the published `topDerivative_zero`. The latter is
itself definitional. No restriction is placed on the module dimension,
nonzeroness, smooth tensor multiplicity or the size of a `GL₀` carrier.

## Import and mathematical proof-dependency audit

The sole direct import is the now-published
`Langlands.Representation.Derivative.PartialDerivativeTensorLocalization`.
Only its `upperCoinvariantsFunctor` definition is used: none of its tensor
quotient comparison theorems is a proof input. Its full paired source was
checked. Its two-lift tensor construction uses only the exact localization
and tensor universal properties, not an ordinary derivative comparison.

Recursive traversal of the actual project `import` declarations gives
exactly 63 modules, listed below, excluding this new entry module. Every
one of their Lean/Markdown pairs is byte-identical to current Library
`7d8c1355c088b76a992b0af1690748d5ae7147b5`. Sixty-two pairs are also
byte-identical to workspace base Library
`a081e0a279cb7346dce7f5afd3dee14f4fbaa60e`; the sole exception is the newly
published `PartialDerivativeTensorLocalization` pair, which did not exist
in that older base. In particular the target statement pair and its entire
dependency closure are unchanged. The independently reviewed tensor unit
is used by its current Lean name.

The actual new proof dependencies are the `Localization.relations` span,
Mathlib quotient equivalence and hom extensionality, the trivial-group
instances, `Mirabolic.rankOne_eq_one`, the published restriction and
`psiMinus` definitions and their induced maps, the definitional rank-cast
and derivative equations just described, and elementary category natural
isomorphism constructors. Their inspected proof bodies are quotient,
matrix-coordinate or definitional calculations. The ordinary derivative
iteration contributes definitions and their equations, with no general
comparison, vanishing or finiteness theorem assumed.

The closure also contains elementary smooth-transfer, twist, admissibility,
matrix-coefficient and Whittaker definitions and laws inherited from the
fixed target. Their admissibility or functional results are unused here.
A broad source scan for the excluded mathematical families found only
arithmetic field/residue-degree uses of `Module.finrank`, the unused
`Category.Basic.HasFiniteLength` predicate, and an unused proposition
`HarmonicAnalysis.IsSelfDual` about Fourier self-duality. Those are neither
representation-finiteness conclusions nor representation-duality inputs.

Every exclusion of the parent task remains binding. Each table row checks
both the actual import closure and the implemented proof dependencies;
its finding also excludes the named conclusions, their proof successors
and their downstream consequences as inputs.

| Excluded family and parent task references | Boundary proof audit |
| --- | --- |
| `SegmentHeadProductIrreducibility` (`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`); `GenericSegmentProductUniqueness` (`30341ae4-65f2-4a0e-9283-763db01a409e`); individual special-head/reverse-socle (`67279e36-f3c2-42e3-9302-11729784042e`) and segment-socle/reverse-head (`4ca79bbd-589e-476b-9f65-661e799984b5`) existence | No segment, head or socle module occurs. The quotient maps use only singleton-group relation spans. |
| Multisegment exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), ordered conversion (`8252833d-c269-41a9-824c-5879e531b23b`) | No multisegment, ordering or coverage theorem occurs. Both inverse maps come from the actual quotient universal property. |
| Tempered uniqueness (`52e97845-36bb-457d-b76f-70753334b88c`), `SquareIntegrableLanglandsClassification` (`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable exhaustion (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`), regular exhaustion (`bf433f0a-921a-428c-b0c0-6475438125ac`), analytic segment classification (`aca8805b-054f-4d56-8045-12db7f623404`), `SegmentSpecialEssentialSquareIntegrability` (`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`) | No classification or square-integrability input occurs. All module carriers are arbitrary. |
| `UnlinkedSegmentSocleProductIrreducible` (`23e98d90-6055-4e35-91a9-b0f5d8a84961`), `LinkedSegmentSocleReverseProductStructure` (`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`), `LinkedSegmentSoclePairReducible` (`8fa9f68b-fa1b-431a-97f6-5b163964d1fc`), `SegmentSocleProductIrreducibility` (`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`), juxtaposed structure and quotient-Hom (`7ff2a1e9-89dc-439e-a861-a567b3db92bf`) | No socle, representation product-structure, reducibility or quotient-Hom theorem occurs. |
| Adjacent socle commutation (`e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`), two-segment commutation (`426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0`), linked gluing (`c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea`), `OrderedMultisegmentSocleExistence` (`23189526-80b0-4828-a6d4-7ebec2cbeef5`), socle exhaustion (`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`) | No socle commutation, gluing or exhaustion module or theorem occurs. |
| `SegmentFullJacquetFormula` (`ed48ae06-964c-4c84-9e62-978f5a953ca7`), `SegmentHeadJacquetFormula` (`55ad1e10-62d8-46b7-a081-909ef0056426`), `SegmentSocleJacquetFormula` (`b95105c6-f8bb-4641-ae53-2f49d1e7f034`), `SegmentSpecialJacquetExponentNormFormula` (`92aea10f-62ac-4e0b-bd4a-9a80909797c5`); all segment derivative formulas and parent six-statement parts (b), (d), (e), (f) | No segment formula is used. `Jacquet.Localization` supplies the general relation quotient; the ordinary derivative equations are inspected unfoldings. |
| `TwoSupercuspidalNonadjacentProductIrreducible` (`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`), `TwoSupercuspidalProductStructure` (`ab61f565-1427-4746-ba77-46097563e962`); Ze80 §§3.5, 9.6, Theorems 4.2, 9.7 and 9.3 | No product criterion, segment derivative, analytic theorem or unproved BZ77 derivative result is used. The first task's Haar bridge is absent. |
| `IrreducibleCoinvariantFinitenessStatement` (`5ab445dc-d2b4-4072-80d1-6370870a4a26`), `LeviCuspidalCoinvariantFinitenessStatement` (`3ff5c8fb-397c-4345-bcb3-5d98a0993d18`), the dependent mirabolic finite-length route (`5428fe2c-013c-482d-aa6e-7df43e7191aa`), `SupercuspidalCoinvariantFinitenessStatement` (`62de5903-b616-4b5c-88eb-a066b77c5467`) | No representation-finiteness input occurs. The finite-length predicate and arithmetic degrees mentioned above are unused by the new proofs. |
| Proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` (`2e5183b1-01e9-44fb-b26c-f4521a25c7c7`) | No classification module occurs. Neither `UpperUnipotentCharacterFactorization` nor `TopDerivativeCoinvariantComparison`, whose closure reaches that host, is imported. No assertion about a derivative's dimension is used. |
| Plus, adjunction, representation duality, derivative filtration, pairing, or unproved general derivative comparisons | No such theorem is used. The dual module only defines linear functionals. The full higher-rank transitivity and top-localization construction remain unproved here. |

### Complete transitive project import list

The list includes the single direct import and excludes this new entry module.

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
