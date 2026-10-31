# One normalized minus step in full upper localization

Author: Worker 1004.

This internal construction specializes the published character-localization
tower to the actual mirabolic groups and the exact determinant-normalized
minus functor. Its final constructor is
`Langlands.Derivative.TopLocalization.stepIso`:

```text
Mirabolic.phiMinus T ψ n ⋙ mirabolicUpperCoinvariantsFunctor ψ.complex n ≅
  mirabolicUpperCoinvariantsFunctor ψ.complex (n + 1).
```

The parameters are `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`,
`T : F.TopologicalData`,
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`,
and arbitrary `n : ℕ`. Every functor type installs `letI := T.topology`.
The source is `SmoothRep.{0,uF,uV} ℂ (mirabolic (n+1) F.Carrier)`, and
the target is `SmoothRep.{0,uF,uV} ℂ (GeneralLinear 0 F.Carrier)`.
Both output actions are trivial on their entire quotient carriers in
`Type uV`; `uF` and `uV` are independent. There are no finite-length,
admissibility, irreducibility, dimension, genericity or nonzero-object
premises. The bundled character's existing continuity and nontriviality
conditions are retained, and the same positive character is used everywhere.

All `n`, including zero, are covered. Since `mirabolic r F` is `P_(r+1)`,
this single step starts at `P_(n+2)` and passes through `P_(n+1)`.
The terminal `P_1` to `GL_0` step, derivative iteration, rank casts,
and the complete all-rank top-derivative and exterior-tensor comparisons
are separate obligations. This module constructs the one-step isomorphism
and its inverse and naturality, without asserting those further comparisons.

## Provenance and original conventions

The convention source is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, original PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original was read at §1.8(b), printed pp.444–445 / PDF pp.5–6,
Proposition 1.9(c), printed p.445 / PDF p.6, and §3.1, printed p.450 /
PDF p.11. Section 1.8(b) defines the quotient by the span of
`π(u)v - θ(u)v` and the negative inverse-half normalization of the remaining
action. Proposition 1.9(c) motivates composing character localizations.
Section 3.1 supplies the last-row mirabolic subgroup, last-column radical,
standard smaller-group embedding and positive last-coordinate character.
No source-specific errata note was found in the supplied project and Library
notes and literature index; this records the extent of the local check.

This module is an internal specialization of the independently published
`Jacquet.Localization.TowerDatum.twistedEquiv` and
`Jacquet.Localization.transportEquiv`, with hypotheses proved for the actual
matrix subgroups. The original transitivity assertion is not an assumed Lean
proof input. The imported tower proves both quotient lifts and both inverse
laws. The actual published `Mirabolic.phiMinus` already uses the explicit
`|det|^(-1/2)` character. Its triviality on the smaller upper group is proved
from determinant one. No identification of this explicit character with a
Haar conjugation modulus is asserted or needed here.

## Actual tower data and subgroup copies

For an object `A`, write `ρ = A.representation`. The declaration
`stepDatum T ψ n : TowerDatum ℂ (mirabolic (n+1) F.Carrier)` uses:

| Tower field | Actual value |
| --- | --- |
| `G` | `mirabolic (n+1) F.Carrier = P_(n+2)` |
| `U` | `radical (n+1) F.Carrier` |
| `M` | `successorSubgroup n F.Carrier` |
| `W` | `upperLeviSubgroup (n+1) F.Carrier` |
| `H` | the bottom subgroup of `G` |
| `θ` | `T.mirabolicTheta ψ n`, the actual positive radical character |
| `η` | `mirabolicUpperCharacter ψ.complex (n+1)` restricted to `W` |
| `Θ` | that same full upper character restricted to `U ⊔ W` |

The published `upper_eq_radical_sup` gives the exact equality
`Mirabolic.upperUnipotent (n+1) F.Carrier = U ⊔ W`. The inclusions,
normalizer condition for `M`, and invariance of `θ` are the published
actual successor-subgroup and character results. The bottom subgroup's
normalizer condition and `η`-invariance follow from its sole element being
one. The restriction of `Θ` to `U` is the positive character identity
`entrywiseCharacter_radical`; the proof applies `congrArg Units.val` to
pass from its units-valued equality to the tower field's coerced scalar
equality. Its restriction to `W` is definitional.

The tower's second subgroup is `W.subgroupOf M`, a distinct subtype group.
`stepInnerEquiv T ψ n` identifies it with the actual smaller
`Mirabolic.upperUnipotent n F.Carrier`. It is the composite of the
published `Mirabolic.upperUnipotentEquiv` and `successorUpperEquiv`.
`stepInnerEquiv_val` proves that its value as an element of `M` is
`successorEquiv u.val`. Thus each transport keeps the actual matrix,
adding or removing only the indicated subgroup certificates.
`stepInnerEquiv_character` is the published `entrywiseCharacter_levi`
identity on this smaller upper group. It matches the tower's
`innerCharacter` exactly, with no inverse or conjugation of `ψ`.

## The normalization on the actual second quotient

`stepTwist T n : M →* ℂˣ` is exactly
`Mirabolic.phiMinusCharacter T n` transported along `successorEquiv.symm`.
The latter character is the published real power with exponent `-(1/2)`
of the determinant norm restricted to the smaller mirabolic group.
The theorem `stepTwist_inner` proves it is one on every element of the
tower's actual inner subgroup: use surjectivity of `stepInnerEquiv`, its
value formula, the inverse law for `successorEquiv`, and the published
`realPowerCharacter_mirabolicUpper T _ u`. That lemma comes from upper
triangular matrices having determinant one, followed by `map_one` for
the normalized norm and the real-power character.

Consequently the second quotient of the *twisted* first action has the
required untwisted smaller upper relations. The first quotient and its
normalization have not been replaced. The tower's supplied final character
is one, and `H` is bottom; only the underlying proved linear equivalence
of `twistedEquiv` is used. Both final functors are already the published
trivial `GL_0` representations on their whole quotient modules.

## The two class maps and naturality

`stepIteratedEquiv` specializes `transportEquiv` to `stepInnerEquiv` and
the identity linear equivalence on the first quotient. The action
compatibility obligation unfolds the actual `phiMinus`: its action at
`u` is the actual normalization scalar times `firstAction` at
`successorEquiv u.val`. Substituting `stepInnerEquiv_val` and the inverse
law gives the tower's `twistedFirstAction` at the corresponding inner
element. The character compatibility is `stepInnerEquiv_character`.
Thus this transport has the actual normalized second quotient as source.

`stepDirectEquiv` specializes `transportEquiv` to
`MulEquiv.subgroupCongr upper_eq_radical_sup.symm` and the identity
coefficient equivalence. It identifies the tower's join quotient with
the actual full upper quotient. Both action and character compatibility
are definitional on the same matrices.

`stepLinearEquiv` composes `stepIteratedEquiv`, the underlying linear
equivalence of the published `stepDatum.twistedEquiv` using
`stepTwist_inner`, and `stepDirectEquiv`. On original representatives:

```text
[[v]_(radical,θ)]_(smaller upper,ψ)  ↦  [v]_(full upper,ψ),
[v]_(full upper,ψ)                  ↦  [[v]_(radical,θ)]_(smaller upper,ψ).
```

The declarations `stepLinearEquiv_mk_mk` and
`stepLinearEquiv_symm_mk` prove these formulas by reflexivity. Both inverse
laws are carried by the composed `LinearEquiv`: `transportEquiv` uses
two quotient lifts and checks their composites on representatives;
`twistedEquiv` similarly constructs its forward and backward lifts and
checks both inverse laws, using the twist-triviality proof for the second
relation. No injectivity, surjectivity or dimension statement is assumed.

`stepIso` bundles these equivalences with `SmoothRep.mkIso` and
`NatIso.ofComponents`. The target actions are the trivial `GL_0` actions,
so equivariance is reflexive. For every smooth mirabolic intertwiner `f`,
the actual `phiMinus` map is the induced quotient map on the same linear
map, and the full upper functor uses `Localization.mapLinear`. Both
naturality composites therefore send the nested class of `v` to the full
class of `f(v)`. The proof applies the smooth/representation hom
extensionality lemmas and then `Localization.hom_ext` twice. The remaining
representative calculation is reflexivity. The constructed `NatIso`
supplies inverse naturality. The final formulas are also exposed as
`stepIso_hom_app_mk_mk` and `stepIso_inv_app_mk`.

## Import and mathematical proof-dependency audit

The three direct imports are the published complete pairs
`Derivative.TopLocalizationData`, `Derivative.TopLocalizationRestriction`
and `Jacquet.LocalizationTower`. Their used definitions and proof bodies,
the complete tower and quotient-transport pairs, and the actual
`MirabolicMinus` construction have been inspected. The focused data and
restriction units were independently accepted and published before use;
the exact supplied-twist tower was likewise independently accepted and
published before this specialization was compiled. No pending draft or
unpublished comparison is used as an input.

Recursive traversal of the actual project imports gives 89 modules,
listed below, excluding this entry module. Every imported Lean/Markdown
pair in the workspace agrees byte for byte with inspected current Library
`3a4a075669d8c6e332c349566f8c1a7f96d2f5e6`. The target
`PartialDerivativeTensorStatement` pair retains its exact contract hashes
(`30c22587bab476fab8c6a190841b30c41f8dfa20b9f40b0187254c3f53227f41`
for Lean and
`e21ce266515ce4c853255f63bd98c8dd5bb097ded93fec62c9c329415b5e8c15`
for Markdown); neither it nor any imported pair was edited here.

The earlier data/restriction publications predate a published elementary
change to `Group.GL.NormalizedCharacter`: it now imports
`Topology.CompactNormCharacter` and adds a determinant-norm identity on
compact subgroups. That helper's complete pair was inspected: its only
imports are Mathlib, and its proof bounds powers and inverses of the
image of a compact subgroup under a continuous positive character. The
historical `RankinSelberg.LastRowReduction` namespace does not import that
consumer. This change is recorded rather than treating the historical
closures as unchanged. Neither the compact-subgroup theorem nor its
proof is used by this construction. The tower's own complete 23-module
closure is unchanged since its publication and contains no derivative,
Whittaker, segment, socle, classification or cuspidal module.

The actual mathematical proof inputs are the elementary matrix join and
subgroup copies, exact character restrictions, determinant-one and
real-power-one lemmas in `TopLocalizationData`; the full upper functor and
character in `TopLocalizationRestriction`; the exact quotient, descended
action and induced maps in `Localization`; the proved twisted quotient
tower in `LocalizationTower`; the proved two-lift equivalence in
`LocalizationTransport`; and the unchanged actual normalized minus-functor
construction in `MirabolicMinus`. Their remaining packaging uses Mathlib
linear equivalences and natural isomorphisms. `PartialDerivativeTensorLocalization`
is imported transitively for the full upper quotient functor only; its
tensor comparison theorem is unused. `MirabolicQuotientMeasure` contributes
only the already inspected elementary matrix membership lemmas to
`TopLocalizationData`; none of its measure construction is a proof input
here. No general BZ77 derivative theorem is assumed.

The closure includes arithmetic field/residue-degree finranks, generic
admissibility and finite-length predicates, elementary twist-preservation
lemmas, the unused Fourier `IsSelfDual` proposition, and the unused
`WhittakerPrerequisitesStatement` proposition. These do not supply any
representation-finiteness, representation-duality or excluded consumer
conclusion. `LocalizationTransport`'s scalar-vanishing lemma is unused.
The following checks retain every parent exclusion, including named
conclusions, proof successors and downstream consequences.

| Excluded family and parent task references | One-step proof audit |
| --- | --- |
| `SegmentHeadProductIrreducibility` (`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`); `GenericSegmentProductUniqueness` (`30341ae4-65f2-4a0e-9283-763db01a409e`); individual special-head/reverse-socle (`67279e36-f3c2-42e3-9302-11729784042e`) and segment-socle/reverse-head (`4ca79bbd-589e-476b-9f65-661e799984b5`) existence | No segment, head or socle module occurs. The inverse maps use the existing quotient transport and supplied-twist tower universal properties. |
| Multisegment exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), ordered conversion (`8252833d-c269-41a9-824c-5879e531b23b`) | No multisegment, ordering or coverage theorem occurs. The two maps send nested representatives to single representatives and back. |
| Tempered uniqueness (`52e97845-36bb-457d-b76f-70753334b88c`), `SquareIntegrableLanglandsClassification` (`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable exhaustion (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`), regular exhaustion (`bf433f0a-921a-428c-b0c0-6475438125ac`), analytic segment classification (`aca8805b-054f-4d56-8045-12db7f623404`), `SegmentSpecialEssentialSquareIntegrability` (`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`) | No classification or square-integrability input occurs. Every original module carrier is arbitrary. |
| `UnlinkedSegmentSocleProductIrreducible` (`23e98d90-6055-4e35-91a9-b0f5d8a84961`), `LinkedSegmentSocleReverseProductStructure` (`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`), `LinkedSegmentSoclePairReducible` (`8fa9f68b-fa1b-431a-97f6-5b163964d1fc`), `SegmentSocleProductIrreducibility` (`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`), juxtaposed structure and quotient-Hom (`7ff2a1e9-89dc-439e-a861-a567b3db92bf`) | No socle, representation product-structure, reducibility or quotient-Hom theorem occurs. |
| Adjacent socle commutation (`e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`), two-segment commutation (`426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0`), linked gluing (`c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea`), `OrderedMultisegmentSocleExistence` (`23189526-80b0-4828-a6d4-7ebec2cbeef5`), socle exhaustion (`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`) | No socle commutation, gluing or exhaustion module or theorem occurs. |
| `SegmentFullJacquetFormula` (`ed48ae06-964c-4c84-9e62-978f5a953ca7`), `SegmentHeadJacquetFormula` (`55ad1e10-62d8-46b7-a081-909ef0056426`), `SegmentSocleJacquetFormula` (`b95105c6-f8bb-4641-ae53-2f49d1e7f034`), `SegmentSpecialJacquetExponentNormFormula` (`92aea10f-62ac-4e0b-bd4a-9a80909797c5`); all segment derivative formulas and parent six-statement parts (b), (d), (e), (f) | No segment formula is used. General localization supplies the relation quotient, and ordinary restriction is its exact published definition. |
| `TwoSupercuspidalNonadjacentProductIrreducible` (`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`), `TwoSupercuspidalProductStructure` (`ab61f565-1427-4746-ba77-46097563e962`); Ze80 §§3.5, 9.6, Theorems 4.2, 9.7 and 9.3 | No product criterion, segment derivative, analytic theorem or unproved BZ77 derivative result is used. No Haar bridge is needed. |
| `IrreducibleCoinvariantFinitenessStatement` (`5ab445dc-d2b4-4072-80d1-6370870a4a26`), `LeviCuspidalCoinvariantFinitenessStatement` (`3ff5c8fb-397c-4345-bcb3-5d98a0993d18`), the dependent mirabolic finite-length route (`5428fe2c-013c-482d-aa6e-7df43e7191aa`), `SupercuspidalCoinvariantFinitenessStatement` (`62de5903-b616-4b5c-88eb-a066b77c5467`) | No representation-finiteness input occurs. The imported finite-length predicate and arithmetic degrees described above are unused. |
| Proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` (`2e5183b1-01e9-44fb-b26c-f4521a25c7c7`) | No classification module occurs. Neither UpperUnipotentCharacterFactorization nor TopDerivativeCoinvariantComparison, whose closure reaches the excluded host, is imported. No derivative dimension is used. |
| Plus, adjunction, representation duality, derivative filtration, pairing, or unproved general derivative comparisons | No such theorem is used. The published generic quotient tower supplies its own quotient-lift proof; no derivative comparison conclusion is used. The all-rank top-localization comparison remains a separate obligation. |

### Complete transitive project import list

The list includes the three direct imports and excludes this entry module.

```text
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientAveragingKernel
Langlands.Analysis.Local.QuotientComplex
Langlands.Analysis.Local.QuotientFunctional
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.QuotientTranslation
Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicProjection
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
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.Partial
Langlands.Representation.Derivative.PartialDerivativeTensorLocalization
Langlands.Representation.Derivative.PartialDerivativeTensorStatement
Langlands.Representation.Derivative.TopLocalizationData
Langlands.Representation.Derivative.TopLocalizationRestriction
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationTower
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.RankOneQuotient
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentQuotient
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
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
Langlands.Representation.Whittaker.MirabolicQuotientMeasure
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
