# The terminal mirabolic full upper quotient

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
theorem are constructed separately, in `TopLocalizationComparison` and
`PartialDerivativeTensorProof`.

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
source. No source-specific errata note was found in the project and
Library notes and literature index in a bounded source check.

The source does not serve as an unproved Lean transitivity input. The only
quotient equivalence used here is the published
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

The sole direct import is the published
`Derivative.TopLocalizationRestriction`. Its complete pair and the used
`Mirabolic`, `MirabolicMinus`, `Localization` and `LocalizationTransport`
constructions were inspected. The restriction module supplies the exact full upper functor and
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

Recursive traversal of the actual project imports at Library commit
`c6045fe1328899de3416096b16eb72db93a6c7fc` gave exactly 66 modules,
listed below, excluding this entry module.

The closure contains the elementary extension of
`Group.GL.NormalizedCharacter` importing
`Topology.CompactNormCharacter`. That complete helper pair was inspected:
it imports Mathlib only, and its compact-character proof bounds powers and
inverses. The historical `RankinSelberg.LastRowReduction` namespace adds no
consumer import. Neither that theorem nor its proof is used here.

The broad source scan finds arithmetic field/residue-degree finranks, generic
admissibility and finite-length predicates and elementary twist-preservation
lemmas, the unused Fourier `IsSelfDual` proposition, and the unused
`WhittakerPrerequisitesStatement` proposition. These do not supply any
representation-finiteness, representation-duality or excluded consumer
conclusion. The following checks of the excluded families cover named
conclusions, successors and transitive consequences as well as the direct
imports.

| Excluded family | Terminal mirabolic proof audit |
| --- | --- |
| `SegmentHeadProductIrreducibility`; `GenericSegmentProductUniqueness`; individual special-head/reverse-socle and segment-socle/reverse-head existence | No segment, head or socle module occurs. The inverse maps use only the existing quotient transport universal property. |
| Multisegment exhaustion, ordered strong-head existence, quotient coverage, ordered conversion | No multisegment, ordering or coverage theorem occurs. Both maps preserve the original quotient representatives. |
| Tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable exhaustion, regular exhaustion, analytic segment classification, `SegmentSpecialEssentialSquareIntegrability` | No classification or square-integrability input occurs. Every original module carrier is arbitrary. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `SegmentSocleProductIrreducibility`, juxtaposed structure and quotient-Hom | No socle, representation product-structure, reducibility or quotient-Hom theorem occurs. |
| Adjacent socle commutation, two-segment commutation, linked gluing, `OrderedMultisegmentSocleExistence`, socle exhaustion | No socle commutation, gluing or exhaustion module or theorem occurs. |
| `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`; all segment derivative formulas | No segment formula is used. General localization supplies the relation quotient; the actual normalized psiMinus is retained at rank zero. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, `TwoSupercuspidalProductStructure`; Ze80 §§3.5, 9.6, Theorems 4.2, 9.7 and 9.3 | No product criterion, segment derivative, analytic theorem or unproved BZ77 derivative result is used. No Haar bridge is needed. |
| `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`, the dependent mirabolic finite-length route, `SupercuspidalCoinvariantFinitenessStatement` | No representation-finiteness input occurs. The imported finite-length predicate and arithmetic degrees described above are unused. |
| Proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` | No classification module occurs. Neither UpperUnipotentCharacterFactorization nor TopDerivativeCoinvariantComparison, whose closure reaches the excluded host, is imported. No derivative dimension is used. |
| Plus, adjunction, representation duality, derivative filtration, pairing, or unproved general derivative comparisons | No such theorem is used. The dual module only defines linear functionals. No tower comparison is used by this terminal module. Higher-rank iteration and the all-rank adapter are constructed in `TopLocalizationComparison`. |

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
