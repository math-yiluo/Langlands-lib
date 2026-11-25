# Rank-zero and rank-one top-localization comparisons

This module constructs the natural comparison between the actual full
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
exterior-tensor theorem are separate: `TopLocalization.topLocalizationIso`
(module `TopLocalizationComparison`) and `partialDerivativeTensor` (module
`PartialDerivativeTensorProof`).

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
in `Mirabolic.psiMinus`. This module makes no Haar-modulus identification.
The rank-zero extension and explicit quotient equivalences are internal
constructions. No filtration, pairing, cuspidal, classification or dimension
conclusion on these or neighboring pages is used. Bounded checks of the
project and Library errata-note locations and literature filenames
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

The sole direct import is the published
`Langlands.Representation.Derivative.PartialDerivativeTensorLocalization`.
Only its `upperCoinvariantsFunctor` definition is used: none of its tensor
quotient comparison theorems is a proof input. Its full paired source was
checked. Its two-lift tensor construction uses only the exact localization
and tensor universal properties, not an ordinary derivative comparison.

Recursive traversal of the actual project `import` declarations gives
exactly 63 modules, listed below, excluding this module. Every
one of their Lean/Markdown pairs is byte-identical to Library
`7d8c1355c088b76a992b0af1690748d5ae7147b5`. Sixty-two pairs are also
byte-identical to the older Library
`a081e0a279cb7346dce7f5afd3dee14f4fbaa60e`; the sole exception is the
`PartialDerivativeTensorLocalization` pair, which did not exist
in that older base.

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
matrix-coefficient and Whittaker definitions and laws imported through the
target statement. Their admissibility or functional results are unused here.
A broad source scan for the excluded mathematical families found only
arithmetic field/residue-degree uses of `Module.finrank`, the unused
`Category.Basic.HasFiniteLength` predicate, and an unused proposition
`HarmonicAnalysis.IsSelfDual` about Fourier self-duality. Those are neither
representation-finiteness conclusions nor representation-duality inputs.

Every exclusion set for the all-rank comparison applies here. Each table row checks
both the actual import closure and the implemented proof dependencies;
its finding also excludes the named conclusions, the modules that prove them
and their downstream consequences as inputs.

| Excluded family | Boundary proof audit |
| --- | --- |
| `SegmentHeadProductIrreducibility`; `GenericSegmentProductUniqueness`; individual special-head/reverse-socle and segment-socle/reverse-head existence | No segment, head or socle module occurs. The quotient maps use only singleton-group relation spans. |
| Multisegment exhaustion, ordered strong-head existence, quotient coverage, ordered conversion | No multisegment, ordering or coverage theorem occurs. Both inverse maps come from the actual quotient universal property. |
| Tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable exhaustion, regular exhaustion, analytic segment classification, `SegmentSpecialEssentialSquareIntegrability` | No classification or square-integrability input occurs. All module carriers are arbitrary. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `SegmentSocleProductIrreducibility`, juxtaposed structure and quotient-Hom | No socle, representation product-structure, reducibility or quotient-Hom theorem occurs. |
| Adjacent socle commutation, two-segment commutation, linked gluing, `OrderedMultisegmentSocleExistence`, socle exhaustion | No socle commutation, gluing or exhaustion module or theorem occurs. |
| `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`; all segment derivative formulas and parts (b), (d), (e), (f) of the six statements of `Classification.SegmentSocleDerivativesStatement` | No segment formula is used. `Jacquet.Localization` supplies the general relation quotient; the ordinary derivative equations are inspected unfoldings. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, `TwoSupercuspidalProductStructure`; Ze80 §§3.5, 9.6, Theorems 4.2, 9.7 and 9.3 | No product criterion, segment derivative, analytic theorem or unproved BZ77 derivative result is used. The Haar bridge introduced with the first of these, `Derivative.MirabolicMinusNormalization`, is absent. |
| `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`, the dependent mirabolic finite-length route, `SupercuspidalCoinvariantFinitenessStatement` | No representation-finiteness input occurs. The finite-length predicate and arithmetic degrees mentioned above are unused by the new proofs. |
| Proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` | No classification module occurs. Neither `UpperUnipotentCharacterFactorization` nor `TopDerivativeCoinvariantComparison`, whose closure reaches the vanishing half of `SupercuspidalDerivatives` (`Classification.SupercuspidalDerivativeVanishing`), is imported. No assertion about a derivative's dimension is used. |
| Plus, adjunction, representation duality, derivative filtration, pairing, or unproved general derivative comparisons | No such theorem is used. The dual module only defines linear functionals. The full higher-rank transitivity and top-localization construction are not proved here. |

### Complete transitive project import list

The list includes the single direct import and excludes this module.

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
