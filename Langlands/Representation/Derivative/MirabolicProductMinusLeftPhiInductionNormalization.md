# Ambient Phi normalization of left orbit compact induction

Author: Worker 499.

This module constructs `leftPhiAmbientInductionEquiv` in
`Langlands.Derivative.MirabolicProductMinus`. It moves the actual ambient
inverse-half determinant character through compact induction from either
actual left stages section, retaining the entire normalized coefficient.
It proves the evaluation formula and naturality for every induced function
and both input maps across independent carrier universes. It also proves
that compact induction of the complete normalized cycle coefficient has
subsingleton carrier. The comparison with localized higher mixed products,
the identity-orbit source comparison, rank transport and the six-part host
theorem remain separate obligations.

## Source and provenance

The original motivation is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b), printed pp.444–445 (one-based PDF pages 5–6), defines
positive-character localization and its inverse-half normalization.
Proposition 1.9(f), printed p.445 (PDF page 6), gives scalar-twist
compatibility with smooth and compact induction. Sections 3.1–3.2,
printed pp.450–451 (PDF pages 11–12), specify the mirabolic character and
minus functors. Section 4.12(II), printed pp.456–457 (PDF pages 17–18),
defines the left mixed product; §4.13(b), printed p.458 (PDF page 19),
states its functorial comparison. Section 7.2, printed p.471 (PDF page 32),
supplies the two left orbit representatives. The task's retained reading
record covers these passages and relevant page images. The bounded
supplied-source and public-note errata search found no applicable BZ77
entry; no global absence is asserted.

The present specialization to actual stages groups, its naturality and
its cycle-vanishing consequence are internal derived content. The original
does not literally state this nested-subgroup interface. The proof uses
the published actual normalized coefficient construction and the published
compact-induction scalar-twist equivalence. Worker 499 wrote this pair;
no peer draft supplies a proof body.

## Parameters, groups and ranks

The declarations quantify arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}`, supplied `T : F.TopologicalData`, all
`k,r : ℕ`, both `i : Fin 2`, and

```text
ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology,
ρ : Representation ℂ GL_(k+1)(F) V,
τ : Representation ℂ P_(r+2)(F) W.
```

The three universes `uF,uV,uW` are independent. Naturality allows independent
target universes `uV',uW'`. Neither input representation needs to be smooth
for these declarations: the compact-induced carriers already consist of
uniformly smooth functions. In the later host application the inputs will
be the actual smooth representations. No admissibility, finite dimension,
irreducibility, finite length, genericity, chosen vector, canonical topology,
universe saturation or comparison premise is added. All original carriers,
including zero representations, are retained.

The Library convention is `mirabolic n F.Carrier = P_(n+1)(F)`. Set

```text
G   = mirabolic (k+r+1) F.Carrier,
L_i = (leftStages k r F.Carrier i).comap plusSuccessor,
S_i = leftPhiNormalizedStabilizer T k r ρ τ i,
A_i = leftPhiStagesAction k r ψ i S_i,
χ   = Mirabolic.phiMinusCharacter T (k+r+1).
```

Thus `G` is the actual output group `P_(k+r+2)`, and `L_i` is its
actual subgroup obtained by pulling back the corresponding higher orbit
stages group through `plusSuccessor`. Index `0` is the cycle representative;
index `1` is identity. The higher source factor is `P_(r+2)`, so the eventual
source minus functor is `phiMinus T ψ r : P_(r+2) → P_(r+1)`.
The ambient minus functor lowers `P_(k+r+3)` to this `G`.
No `P_0`, Phi-minus on `P_1` or rank-zero GL input is introduced.
There is no rank cast in this unit; the later identity-section transport
along `k+1+r = k+r+1` remains an assembly obligation.

Each declaration explicitly installs `T.topology` and
`T.generalLinearTopologicalGroup (k+r+2)`. These supply the actual mirabolic
and subgroup topological-group instances. The smooth ambient character is
exactly `χ` equipped with the published
`Mirabolic.isOpen_ker_phiMinusCharacter T (k+r+1)`. No extra topology or
open-kernel premise is assumed.

## The actual normalized coefficient and induced equivalence

The published `S_i` is the full higher normalized inducing coefficient on
the actual stabilizer: the tensor representation pulled back through the
actual orbit coefficient map and twisted by the higher left covariance.
The published `A_i` acts on the entire nested positive-character quotient
of that coefficient. Define

```text
B_i = leftPhiNormalizedStagesAction T k r ρ τ ψ i.
```

By its actual definition,

```text
B_i = twist (χ.comp L_i.subtype) A_i.
```

The ambient character is the explicit determinant inverse-half character;
no scalar factor is replaced or dropped. In particular the higher
covariance in `S_i` remains present when this additional ambient twist is
moved into the coefficient.

`leftPhiAmbientInductionEquiv` specializes the published
`compactInductionTwistEquiv` to `L_i`, `χ` with its proved open kernel,
and `A_i`. Its exact type is

```text
Representation.Equiv
  (twist χ (compactInduced L_i A_i))
  (compactInduced L_i B_i).
```

Both sides use the actual space `CompactFunctions`: covariant functions
on all of `G`, with a uniform open right stabilizer and compact support
modulo the subgroup. The inherited equivalence multiplies each value
by `χ(l)`; its inverse multiplies by `χ(l)⁻¹`. The generic published proof
checks covariance, intersects the original open stabilizer with the
character kernel, and proves exact equality of projected nonzero supports.
It therefore preserves compactness in both directions and is a genuine
linear representation equivalence on these complete carriers.

`leftPhiAmbientInductionEquiv_eval` states, for every such function `z`
and every `l : G`,

```text
eval L_i B_i (leftPhiAmbientInductionEquiv ... i z).val l
  = (χ l : ℂ) • eval L_i A_i z.val l.
```

This follows by the definitions of the actual specialization and the
published generic equivalence. No measure choice or normalization premise
enters this scalar multiplication.

## Entire-function naturality

For arbitrary intertwiners `f : ρ.IntertwiningMap ρ'` and
`g : τ.IntertwiningMap τ'`, write

```text
m_i = leftPhiStagesMap k r ψ i
        (leftPhiNormalizedStabilizerMap T k r ρ τ f g i),
n_i = leftPhiNormalizedStagesMap T k r ρ τ ψ f g i.
```

The first is the actual quotient-induced map from the entire stages
coefficient `A_i` to its target-input analogue. The second twists this
same underlying map by the ambient restricted character; it intertwines
the full normalized actions `B_i`. Both are induced by the actual tensor
input map, with the higher covariance retained.

For every `z : CompactFunctions L_i A_i`,
`leftPhiAmbientInductionEquiv_natural` proves

```text
E'_i (compactInducedMap L_i m_i z)
  = compactInducedMap L_i n_i (E_i z),
```

where `E_i` and `E'_i` are the corresponding ambient equivalences.
The source map on the left also underlies the map between the ambient
twisted source representations. The proof applies three subtype
extensionality steps and function extensionality, then the scalar-linearity
of the actual coefficient map. It proves equality for all functions and all
input intertwiners, across four independent carrier universes. It is not
limited to representatives or same-universe inputs.

## Vanishing of compact induction from the cycle coefficient

`leftPhiNormalizedInduced_zero_subsingleton` has conclusion

```text
Subsingleton (CompactFunctions L_0 B_0).
```

The proof installs the published
`leftPhiNormalizedStagesQuotient_zero_subsingleton`, which says that the
entire actual normalized cycle coefficient carrier is zero. A function
into a subsingleton type is unique; the equivariance, smoothness and compact
support subtypes inherit this property. The conclusion is therefore about
the complete compact-induced function carrier. It does not select or
truncate a subspace, infer dimension from a character identity, or assert
the vanishing of the higher mixed-product localization without the
separate stages and restriction comparisons.

## Import and mathematical dependency audit

The two direct project imports are

```text
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Induction.CharacterTwistProof
```

The full direct and transitive closure has 93 project modules,
excluding this entry. All 186 imported Lean/Markdown files are nonempty,
byte-identical to the published Library and checked against its manifest at
commit `46311733bb8c7e91d5c932b568a8f16981d98999`.
No pending module or peer draft is imported. In particular the separate
actual character-stages comparison and normalized source coefficient
comparison are not inputs.

The direct mathematical inputs are the published compact-induction
scalar-twist equivalence, the actual ambient character and its open kernel,
the actual normalized stages action and input maps, the proved full cycle
coefficient vanishing, and linearity/function extensionality. Transitively
these use explicit matrix radical and determinant calculations, actual
positive-character localization, tensor quotient algebra, smooth function
stabilizers, support preservation and the existing smooth pullback and
twist infrastructure. The generic compact-induction proof uses no measure
or compact-open basis. The admissibility and Whittaker modules in the
closure contribute no finiteness result or admissibility hypothesis.

| Condition | Actual dependency finding |
| --- | --- |
| Six host conclusions | The host statement and proof modules are absent. No mixed-minus compatibility or boundary conclusion supplies an input. This unit proves only the actual ambient induction normalization and cycle-induced vanishing. |
| Plus functors, adjunction and §4.13(d) | None supplies an input. The plus subgroup and successor used to name the stages section are elementary matrix constructions. |
| General Leibniz and derivative formulas | No Leibniz theorem, unproved BZ77 comparison, Ze80 §3.5 or §9.6 formula, or segment derivative formula is used. |
| Individual head and socle existence | Neither individual special-head/reverse-socle nor segment-socle/reverse-head existence supplies an input. |
| Linked and unlinked segment conclusions | No unlinked irreducibility, linked reverse-product structure, pair reducibility, juxtaposed reverse-product structure or reverse-product quotient homomorphism is used. |
| Segment products, commutation and gluing | No segment-socle product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, Ze80 4.2 or 9.7 criterion, or consequence is used. |
| Segment Jacquet formulas | No full, head, socle or special-exponent Jacquet formula, successor or downstream conclusion supplies an input. |
| Special-head criterion and generic uniqueness | Neither special-head product irreducibility nor generic segment-product uniqueness is used. |
| Ordered existence, coverage and exhaustion | No ordered multisegment-socle or strong-head existence, socle or special-head exhaustion, quotient coverage or ordered conversion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable Langlands classification, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. |
| Two-supercuspidal consumers | Neither nonadjacent-product irreducibility, two-supercuspidal product structure nor full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) is used. |
| Supercuspidal and all-character finiteness | No supercuspidal, all-character single-block or arbitrary-character coinvariant-finiteness theorem or downstream consequence is used. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion or prohibited mirabolic finite-length route supplies an input. |
| Generality and normalization | All `k,r`, both actual orbits, supplied `T`, positive GL input rank and entire arbitrary carriers are retained. Both higher covariance and the actual ambient inverse-half character are present. No input smoothness premise is needed here. |
| Published-input requirement | Every imported pair is published and unchanged. Prop-valued statement definitions, source formulas, drafts, pending constructions and consumer tasks provide no unproved comparison premise. |
| Separate owners and controls | This unit does not duplicate the separate restriction-sequence or exactness work. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |

A scan of this module and its full project closure finds no occurrence in
Lean code of the host's 38 excluded task identifiers or 24 named consumer
declarations, and no proof holes, new axioms or unsafe evaluation commands.
Excluded names in explanatory Markdown are audit prose. Successful
development compilation is distinct from independent semantic acceptance
and publication.

## Complete project import closure

The list below includes every direct and transitive project import,
excluding this entry module. Mathlib is supplied by the pinned authorized
environment and is outside this project-module list.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients
Langlands.Group.GL.MirabolicMixedOrbitSections
Langlands.Group.GL.MirabolicMixedOrbitStages
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CharacterTwistProof
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SplitKernelCharacterExtension
Langlands.Representation.Induction.SplitKernelLocalizationData
Langlands.Representation.Induction.SplitKernelSectionAction
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesRetraction
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
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
Langlands.Representation.Tensor.Finite
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
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
