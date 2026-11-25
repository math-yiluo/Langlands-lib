# Full upper localization and the normalized top derivative in every rank

This internal construction supplies the all-rank natural isomorphism
`Langlands.Derivative.TopLocalization.topLocalizationIso`:

```text
PartialTensor.upperCoinvariantsFunctor ψ.complex m ≅ topDerivative T ψ m.
```

Its parameters are `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`,
`T : F.TopologicalData`,
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`,
and every `m : ℕ`. Each functor type installs `letI := T.topology`.
The source category is
`SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier)` and the target category
is `SmoothRep.{0,uF,uV} ℂ (GeneralLinear 0 F.Carrier)`. The independent
field and carrier universes are preserved. The bundled character's existing
continuity, unitarity and nontriviality conditions are retained; no further
condition on it is imposed.

The left functor takes the quotient of the entire representation carrier by
the actual full upper-unipotent character relations and gives that quotient
the trivial `GL₀` action. The right functor is exactly the published
`generalLinearDerivative T ψ m m (Nat.le_refl m)` followed by
`generalLinearRankCast T (Nat.sub_self m)`. Its determinant inverse-half
normalizations and rank transports are retained. The isomorphism consists
of actual smooth equivariant components with inverses and naturality for
every source morphism. All carriers remain in `Type uV`, with arbitrary
`GL₀` multiplicities. There are no positivity, finite-length, admissibility,
irreducibility, genericity, nonzero-object or dimension premises.

In particular `m = 0` and `m = 1` are covered. At zero the full upper
quotient is naturally the identity on every smooth `GL₀` representation.
At one the construction restricts to `P₁` and takes the actual normalized
`Ψ⁻` quotient. The exterior-tensor comparison is assembled in the
separate module `PartialDerivativeTensorProof`; this module supplies the
shared all-rank adapter.

## Provenance and original conventions

The convention source is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, original PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original was read at §1.8(b), printed pp.444–445 / PDF pp.5–6,
Proposition 1.9(c), printed p.445 / PDF p.6, §3.1, printed p.450 / PDF p.11,
and §3.5 with footnote 2, printed p.452 / PDF p.13. These passages give
the relation-span quotient, negative inverse-half normalization,
localization transitivity, actual mirabolic/radical conventions, and
iteration of the minus functors. No source-specific errata note was found
in a bounded check of the project notes and literature index.

This is an internal categorical consequence of published quotient
constructions. It does not assume the source's
transitivity or a general derivative comparison as a Lean proof input.
The published `TopLocalizationStep` proves the concrete normalized step
using the two quotient lifts and inverse laws in `LocalizationTower` and
`LocalizationTransport`. `TopLocalizationMirabolicZero` proves the
terminal step using the actual `P₁` subgroup identity, and
`TopLocalizationBoundary` proves the `GL₀` boundary. The iteration and
exact rank transports below assemble those proved inputs with the
unchanged derivative definitions. No identification with a Haar
conjugation modulus is needed; the exact explicit inverse-half characters
in the published minus functors are used.

## Implemented iteration, components and naturality

Write `Q_r` for `mirabolicUpperCoinvariantsFunctor ψ.complex r`, so its
source is the actual `P_(r+1)`. The declaration
`mirabolicIteratedIso T ψ n` has type

```text
Q_(0+n) ≅ phiMinusIterate T ψ 0 n ⋙ Q_0.
```

At `n = 0`, `phiMinusIterate` is the identity functor; the inverse left
unitor gives the required comparison. At a successor, the construction
composes:

1. the inverse of the published `stepIso T ψ (0+n)`;
2. the induction isomorphism precomposed with the actual normalized
   `Mirabolic.phiMinus T ψ (0+n)`;
3. the inverse functor associator.

The published successor definition of `phiMinusIterate` identifies the
target functor. The rank expression `0+n` keeps each dependent source
category definitionally equal to the one required by that definition.
Each inverse step sends a single full-upper class of `v` to the smaller
upper class of the actual first radical class of `v`. Its inverse flattens
those nested classes. The positive character is the same at each stage.
The determinant inverse-half scalar is part of the actual first quotient
action; its triviality on the smaller upper subgroup was proved in the
published one-step module from determinant one. Thus induction retains both
maps on whole quotient modules, rather than merely a surjection or a
dimension equality.

`mirabolicLocalizationIso T ψ n` composes this iteration isomorphism with
the published `mirabolicZeroIso T ψ.complex` precomposed by
`phiMinusIterate T ψ 0 n`. The latter sends the terminal full-upper class
to the actual normalized `Ψ⁻` radical class and back on the same original
representative. The target is definitionally
`mirabolicDerivative T ψ 0 n`, namely the actual phi-minus iterate followed
by `Mirabolic.psiMinus T 0`.

`positiveLocalizationIso T ψ n` first uses
`upperRestrictionIso T ψ.complex (0+n)` to identify the full upper
quotient of a `GL_(0+n+1)` representation with the same quotient after
restriction to its actual mirabolic subgroup. That published equivalence
changes only subgroup certificates, keeping the representative vector.
It then precomposes `mirabolicLocalizationIso` with
`generalLinearRestriction T (0+n)`. The target is definitionally the
unchanged `generalLinearDerivativePositive T ψ 0 n`.

Every step above is composition or precomposition of actual natural
isomorphisms. Their forward components send a full-upper class to the
nested radical classes of the same vector, largest rank first, ending in
the `Ψ⁻` class; the inverse components flatten these classes in reverse
order. The imported quotient-lift proofs supply both inverse laws.
For any smooth source intertwiner `f`, the quotient maps at every level
are induced by the same `f`, so both naturality composites send the class
of `v` to the corresponding nested class of `f(v)`. The categorical
composition retains this naturality, inverse naturality and equivariance
without a restriction on the representation or on the morphism.

## Exact rank transports and the final comparison

`upperRankCastIso T ψ h`, for `h : a = b`, compares

```text
PartialTensor.upperCoinvariantsFunctor ψ a ≅
  generalLinearRankCast T h ⋙ PartialTensor.upperCoinvariantsFunctor ψ b.
```

Equality elimination reduces `h` to a reflexive proof. The actual published
rank cast is then the identity functor, and the inverse left unitor gives
the isomorphism. It transports the entire quotient and its induced maps
along `h`; there is no change of rank convention.

`topDerivative_succ T ψ n` composes `topDerivative_eq` with the published
`generalLinearDerivative_top_succ`. The resulting equation is exactly

```text
topDerivative T ψ (n+1) =
  generalLinearRankCast T (Nat.zero_add (n+1)).symm ⋙
    generalLinearDerivativePositive T ψ 0 n.
```

In particular this equation accounts for the final cast from
`(n+1)-(n+1)` to zero in the top-derivative definition; it retains the
source cast along `(Nat.zero_add (n+1)).symm`.

Finally `topLocalizationIso T ψ` is defined by cases on `m`. At zero it is
the published `topLocalizationZeroIso T ψ`, whose forward
component sends the quotient class of `v` to `v` and whose inverse is the
actual quotient map. At `m = n+1` it composes `upperRankCastIso` for that
exact source equality, `positiveLocalizationIso` precomposed by that rank
cast, and the inverse `eqToIso` of `topDerivative_succ`. The resulting
source and target are exactly the functors in the opening declaration.
Forward and inverse components include these actual equality transports;
all quotient formulas described above are read along them.

The output on the right is the actual normalized top derivative as a
representation of the empty-matrix group `GL₀`. That group is
subsingleton, while its representation carriers remain arbitrary. Both
the terminal comparison and the rank-zero boundary use the representation
identity law to prove equivariance, so no carrier is replaced by a
one-dimensional representation. Naturality of the final comparison follows
from composition of its natural isomorphisms, including the rank transport
and equality isomorphisms.

## Import and mathematical proof-dependency audit

The four direct project imports are the published
complete pairs `Derivative.TopLocalizationBoundary`,
`Derivative.TopLocalizationRestriction`, `Derivative.TopLocalizationStep`,
and `Derivative.TopLocalizationMirabolicZero`.
`Mathlib.CategoryTheory.Whiskering` supplies precomposition of natural
isomorphisms. The full pairs, used constructions and proof bodies of these
helpers, the unchanged `Iteration`, `MirabolicMinus`, `Localization`,
`LocalizationTransport`, and the supplied-twist `LocalizationTower` were
inspected.

Recursive traversal at Library commit
`c5eebf94883144ce00adc4e252995c28082f08a7` gave exactly 92 project imports,
listed below, excluding this entry module. This closure
is the 89-import closure of `TopLocalizationStep` together with the
step itself, the terminal module and the boundary module.

The mathematical inputs used by this assembly are exactly the concrete
normalized one-step equivalence, the terminal and rank-zero equivalences,
the GL-to-mirabolic restriction equivalence, the derivative recursion and
rank-cast definitions/equations, equality elimination, and categorical
unitors, associators, precomposition and composition. The lower step uses
elementary matrix subgroup joins, exact positive-character restrictions
and determinant-one identities from `TopLocalizationData`, plus the proved
quotient lifts from `LocalizationTower` and `LocalizationTransport`.
The terminal and boundary use rank-one and rank-zero matrix identities and
the same quotient universal property. This chain supplies inverses and
naturality at each level.

The tensor comparison in the transitively imported
`PartialDerivativeTensorLocalization` is unused; that module supplies the
full-upper functor. The `MirabolicQuotientMeasure` dependency supplies
elementary matrix membership facts to `TopLocalizationData`; its measure
theorems are unused. The closure includes arithmetic field/residue-degree
finranks, generic admissibility and finite-length predicates and elementary
twist-preservation lemmas, the unused Fourier `IsSelfDual` proposition and
the unused `WhittakerPrerequisitesStatement` proposition. None supplies an
excluded representation-finiteness, duality or consumer conclusion.
The scalar-vanishing lemma in `LocalizationTransport` is unused.

The closure contains the elementary extension of
`Group.GL.NormalizedCharacter` importing `Topology.CompactNormCharacter`.
That complete helper pair was inspected: it imports only Mathlib and
proves its compact-character claim by bounded powers and inverses. The
historical `RankinSelberg.LastRowReduction` namespace imports no consumer.
Neither its compact-subgroup result nor its proof is used here.

The following condition-by-condition audit respects every exclusion
below, including named conclusions, the modules that prove them and transitive
consequences.

| Excluded family | All-rank proof audit |
| --- | --- |
| `SegmentHeadProductIrreducibility`; `GenericSegmentProductUniqueness`; individual special-head/reverse-socle and segment-socle/reverse-head existence | No segment, head or socle module occurs. The inverse maps use the existing quotient transport and supplied-twist tower universal properties. |
| Multisegment exhaustion, ordered strong-head existence, quotient coverage, ordered conversion | No multisegment, ordering or coverage theorem occurs. The two maps send nested representatives to single representatives and back. |
| Tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable exhaustion, regular exhaustion, analytic segment classification, `SegmentSpecialEssentialSquareIntegrability` | No classification or square-integrability input occurs. Every original module carrier is arbitrary. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `SegmentSocleProductIrreducibility`, juxtaposed structure and quotient-Hom | No socle, representation product-structure, reducibility or quotient-Hom theorem occurs. |
| Adjacent socle commutation, two-segment commutation, linked gluing, `OrderedMultisegmentSocleExistence`, socle exhaustion | No socle commutation, gluing or exhaustion module or theorem occurs. |
| `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`; all segment derivative formulas | No segment formula is used. General localization supplies the relation quotient, and ordinary restriction is its exact published definition. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, `TwoSupercuspidalProductStructure`; Ze80 §§3.5, 9.6, Theorems 4.2, 9.7 and 9.3 | No product criterion, segment derivative, analytic theorem or unproved BZ77 derivative result is used. No Haar bridge is needed. |
| `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`, the dependent mirabolic finite-length route, `SupercuspidalCoinvariantFinitenessStatement` | No representation-finiteness input occurs. The imported finite-length predicate and arithmetic degrees described above are unused. |
| Proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` | No classification module occurs. Neither UpperUnipotentCharacterFactorization nor TopDerivativeCoinvariantComparison, whose closure reaches the vanishing half of `SupercuspidalDerivatives` (`Classification.SupercuspidalDerivativeVanishing`), is imported. No derivative dimension is used. |
| Plus, adjunction, representation duality, derivative filtration, pairing, or unproved general derivative comparisons | No such theorem is assumed. The all-rank isomorphism is constructed from the published one-step, terminal, restriction and boundary equivalences using derivative recursion and categorical composition. The generic tower proves its own quotient lifts; no unproved general derivative result is a premise. |

### Complete transitive project import list

The list includes the four direct project imports and excludes this entry module.

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
Langlands.Representation.Derivative.TopLocalizationBoundary
Langlands.Representation.Derivative.TopLocalizationData
Langlands.Representation.Derivative.TopLocalizationMirabolicZero
Langlands.Representation.Derivative.TopLocalizationRestriction
Langlands.Representation.Derivative.TopLocalizationStep
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
