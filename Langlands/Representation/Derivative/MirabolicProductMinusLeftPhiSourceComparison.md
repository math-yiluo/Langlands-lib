# Normalized left-Phi identity coefficient comparison

Author: Worker 499.

This module constructs `leftPhiNormalizedSourceEquiv` in
`Langlands.Derivative.MirabolicProductMinus`. It is a representation
equivalence from the entire normalized identity-orbit stages coefficient to
the actual normalized source-Phi coefficient, pulled back through the actual
section equivalence and its proved rank transport. The equivalence is natural
in both representation inputs, across four independent carrier universes.
This is a coefficient comparison for BZ77 §4.13(b). Compact induction,
ambient normalization of the induced representation, and the six-part host
compatibility theorem remain separate obligations.

## Source and provenance

The original motivation is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b), printed pp.444–445 (one-based PDF pages 5–6), defines
positive-character localization and its normalized normalizing-subgroup
action. Sections 3.1–3.2, printed pp.450–451 (PDF pages 11–12), specify the
mirabolic groups, positive character and minus functors. Section 4.12(II),
printed pp.456–457 (PDF pages 17–18), defines the left mixed product;
§4.13(b), printed p.458 (PDF page 19), states its functorial comparison.
Section 7.2, printed p.471 (PDF page 32), supplies the two left orbit
representatives. These passages and relevant page images were read during
this task. The bounded supplied-source and public-note errata search found
no applicable BZ77 entry; no global absence is asserted.

The present full representation equivalence, continuity adapters and
naturality proof are internal derived content. The original does not
literally state this nested-subgroup coefficient interface. The proof
compares the published actual normalized section action and actual
source-Phi coefficient action. The full linear equivalence and the actual
input maps are supplied by their published constructions. No host
compatibility or compact-induction comparison is assumed. Worker 499 wrote
this pair; no peer draft supplies a proof body.

## Parameters and rank transport

The group equivalence `leftPhiLowerSectionEquiv` uses arbitrary
`R : Type uF` with `[CommRing R]`, and all `k,r : ℕ`. With any
`[TopologicalSpace R]`, its forward and inverse functions are continuous;
no topological-ring assumption is needed for these subtype and rank maps.

The coefficient declarations quantify arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}`, supplied `T : F.TopologicalData`, and all
`k,r : ℕ`, including zero. They install exactly `T.topology` where the
actual smooth representations and character require it. The inputs are

```text
ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology,
ρ : Representation ℂ GL_(k+1)(F) V,
B : SmoothRep ℂ P_(r+2)(F).
```

The GL representation is arbitrary; the second input is the actual smooth
representation required by the existing source-Phi functor. Its carrier
universe `uW` is independent of `uV` and `uF`. Naturality permits independent
target carrier universes `uV',uW'`. No admissibility, finite dimension,
irreducibility, finite length, genericity, chosen vector, canonical topology,
universe saturation or assumed comparison is imposed. Zero representations
and all original carriers are retained.

Set

```text
L₁ = (leftStages k r F.Carrier 1).comap plusSuccessor,
H  = leftSubgroup (k+1) r F.Carrier,
e  = leftPhiLowerSectionEquiv k r F.Carrier : L₁ ≃* H.
```

Index `1` is the actual identity orbit. The equivalence `e` is the composite
of `leftPhiStagesSectionEquiv k r 1` with
`leftIdentitySectionEquiv k r F.Carrier`. The first removes redundant stages
membership. The second retains the actual inverse rank transport along the
proved equality

```text
k+1+r = k+r+1.
```

Thus `L₁` lies in `mirabolic (k+r+1) F.Carrier` and `H` lies in
`mirabolic (k+1+r) F.Carrier`. Both realize the output group `P_(k+r+2)`,
but their actual transport is kept in the definition. The higher mixed
product has GL rank `k+1`, source factor `P_(r+2)`, and ambient group
`P_(k+r+3)`. The source functor is exactly
`phiMinus T ψ r : P_(r+2) → P_(r+1)`, with the Library convention
`mirabolic n F.Carrier = P_(n+1)(F)`. No `P_0` or Phi-minus on `P_1`
is introduced.

`continuous_leftPhiLowerSectionEquiv` proves continuity of the intermediate
stages equivalence by its subtype-value function, then composes with the
published continuous rank equivalence. The proof explicitly identifies the
composite function. The inverse proof composes the published continuous
inverse rank map with the reverse subtype map. These theorems preserve
the existing group operations and topologies.

## Actual normalized representations

Write

```text
Q = leftPhiNormalizedStagesQuotient T k r ρ B.representation ψ 1,
A = leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1,
C = leftPhiSourceCoefficient T k r ψ ρ B.
```

The published `Q` is the entire quotient of `V ⊗[ℂ] B` by the actual
nested stabilizer-intersection character relations. The action `A` includes
the full higher covariance and the ambient inverse-half determinant
character on the actual stages section. Its underlying linear equivalence

```text
E = leftPhiNormalizedStagesTensorEquiv T k r ρ B.representation ψ
    : Q ≃ₗ[ℂ] V ⊗[ℂ] ((Mirabolic.phiMinus T ψ r).obj B)
```

is the published complete quotient identification. The source-Phi object
here is the actual character quotient with its normalized successor action.
The lower coefficient `C` is exactly the lower left covariance twist of
the external tensor action of `ρ` and this source-Phi object.

`leftPhiTransportedSourceCoefficient` defines `C.comp e.toMonoidHom`.
Consequently its carrier is the entire tensor with the source-Phi object,
and its action is the actual lower mixed-product inducing coefficient at
the actual rank-transported section element. It contains no replacement
character, selected submodule or quotient of the source-Phi carrier.

## Action comparison and full equivalence

For every `l : L₁`, `v : V` and `w : B`,
`leftPhiNormalizedSource_action_tmul` proves

```text
E (A l [v ⊗ w])
  = (C.comp e.toMonoidHom) l
      (v ⊗ Mirabolic.phiMinusQuotient T ψ r B w).
```

It composes the two published equalities
`leftPhiNormalizedStagesTensorEquiv_action_tmul` and
`leftPhiSourceCoefficient_tmul_quotient`, reversing the latter.
Their common expression is the full
`leftPhiSectionCharacter T (k+1) r (e l)` scalar times the tensor of
the lower GL action and the actual quotient of the source successor action.
The actual inverse-half determinant and lower covariance already agree
by the published normalization calculation. The composite `e` makes their
section arguments agree definitionally. No residual scalar or unproved
character identity is suppressed.

`leftPhiNormalizedSourceEquiv` uses `E` as its underlying linear
equivalence. For each `l`, its intertwining proof applies the published
quotient `hom_ext` and `TensorProduct.ext'`, reducing equality of the two
linear maps on the full quotient to the pure-tensor equality above.
Thus equivariance is proved on every element of `Q`, not only on named
representatives. Bijectivity is supplied by the full published linear
equivalence. The exported representative formula is

```text
leftPhiNormalizedSourceEquiv ... [v ⊗ w]
  = v ⊗ Mirabolic.phiMinusQuotient T ψ r B w.
```

This is `leftPhiNormalizedSourceEquiv_mk_tmul`.

## Actual maps and naturality

Let `f : ρ.IntertwiningMap ρ'` and
`g : B.representation.IntertwiningMap B'.representation`. The inputs and
targets have four independent carrier universes. The definition
`leftPhiTransportedSourceMap` pulls back the published
`leftPhiSourceCoefficientMap ... f g` through the same actual equivalence
`e`. Its underlying linear map is exactly

```text
TensorProduct.map f.toLinearMap
  (mapLinear (radical (r+1) F.Carrier) (Mirabolic.theta ψ r) g).
```

The second map is the actual relation-quotient map underlying
`phiMinus.map`; the source normalization is present in its representation
intertwining property.

For every `z : Q`, `leftPhiNormalizedSourceEquiv_natural` proves

```text
E' (leftPhiNormalizedStagesMap ... f g 1 z)
  = leftPhiTransportedSourceMap ... f g (E z).
```

The proof applies the published full-quotient theorem
`leftPhiNormalizedStagesTensorEquiv_natural`. The actual pulled-back source
map and the representation equivalence reduce to exactly its linear maps.
The exported quotient argument explicitly installs `T.topology`.
This is naturality for all elements and all input intertwiners, not a
same-universe specialization or a formula limited to pure tensors.

## Import and mathematical dependency audit

The two direct project imports are

```text
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
```

The full direct and transitive closure has 92 project modules, excluding
this entry. All 184 imported Lean/Markdown files are nonempty,
byte-identical to the published Library and checked against its manifest at
commit `8c5ba55d80ead022f06e4c04ae7621d1f734bac3`.
No pending module or peer draft is imported. In particular, the separate
actual character-stages compact-induction comparison is not an input.

The mathematical proof dependencies are the actual orbit groups, section
and rank equivalences, the proved normalized radical-quotient identification,
the proved tensor quotient equivalence, the actual source-Phi coefficient
action and map, and linear extensionality. Transitively these use explicit
matrix radical and determinant calculations, actual character localization,
linear transport and tensor algebra, the existing minus construction,
and the smooth pullback, twist and quotient infrastructure. The
admissibility and Whittaker infrastructure appearing transitively contributes
no admissibility hypothesis or coinvariant-finiteness result. No
compact-induction equivalence or host compatibility supplies a proof input.

| Condition | Actual dependency finding |
| --- | --- |
| Six host conclusions | The host statement and proof modules are absent. No mixed-minus compatibility or boundary conclusion supplies an input. This unit proves only the normalized identity coefficient representation comparison. |
| Plus functors, adjunction and §4.13(d) | None supplies an input. The plus subgroup, projection and successor are elementary matrix constructions. |
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
| Generality and normalization | All `k,r`, arbitrary supplied `T`, positive GL input rank and entire carriers are retained. Only the actual source-Phi input is required smooth. Both the ambient inverse-half character and the lower source normalization are present in the compared actions. |
| Published-input requirement | Every imported pair is published and unchanged. Prop-valued statement definitions, source formulas, drafts, pending constructions and consumer tasks provide no unproved comparison premise. |
| Separate owners and controls | This coefficient unit does not duplicate the separate restriction-sequence or exactness work. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |

A scan of this module and its full project closure finds no occurrence in
Lean code of the host's 38 excluded task identifiers or 24 named consumer
declarations, and no proof holes, new axioms or unsafe evaluation commands.
Excluded names in explanatory Markdown are audit prose. Successful
development compilation is distinct from independent semantic acceptance
and publication.

## Complete project import closure

The list below includes every direct and transitive project import,
excluding this entry module. Mathlib is supplied by the pinned authorized
environment and remains unchanged.

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
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SplitKernelCharacterExtension
Langlands.Representation.Induction.SplitKernelLocalizationData
Langlands.Representation.Induction.SplitKernelSectionAction
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesRetraction
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
