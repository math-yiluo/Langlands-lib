# Actual normalized left identity compact-induction comparison

Author: Worker 499.

This module constructs `leftPhiCompactSourceEquiv` in
`Langlands.Derivative.MirabolicProductMinus`. Compact induction of the entire
normalized identity-orbit stages coefficient is representation-equivalent to
compact induction of the actual lower source-Phi coefficient, pulled back
along the proved continuous mirabolic rank map. The equivalence is natural
in both inputs across four independent carrier universes. This is an internal
step toward BZ77 §4.13(b); it does not prove the host compatibility or identify
the localized mixed product with the stages induction.

## Source and provenance

The original motivation is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b) and Proposition 1.9(f), printed pp.444–445 (one-based PDF
pages 5–6), give character localization, normalized normalizer actions and
induction comparisons. Sections 3.1–3.2, printed pp.450–451 (PDF pages
11–12), specify the mirabolic groups and minus functors. Section 4.12(II),
printed pp.456–457 (PDF pages 17–18), defines the left mixed product;
§4.13(b), printed p.458 (PDF page 19), states its natural compatibility.
Section 7.2, printed p.471 (PDF page 32), describes the two left orbit
representatives. These passages and relevant page images were read during
this task. The bounded supplied-source and public-note errata search found
no applicable BZ77 entry; no global absence is asserted.

The continuous rank adapter and this compact-function equivalence are
internal derived content. The original does not literally state these
nested stages interfaces. This module applies the published
`Induction.compactInducedTransport` to the published full normalized source
coefficient equivalence; it does not introduce a second generic transport
construction. The latter theorem's inverse gives the desired direction.
The naturality proof is pointwise, using the published full coefficient
naturality. No peer draft or unpublished construction supplies a proof
body; the pending ambient-normalization unit is not imported.

## Generality and actual ranks

The rank declarations use arbitrary `R : Type uF` with `[CommRing R]` and
`[TopologicalSpace R]`, and every `k,r : ℕ`. They need no topological-ring
hypothesis. The compact-induction declarations quantify arbitrary
`{p : ℕ} [Fact p.Prime]`, `{F : PadicField.{uF} p}`, supplied
`T : F.TopologicalData`, and every `k,r : ℕ`, including zero. All required
topologies are exactly `T.topology`; the topological group instances are
proved by `T.generalLinearTopologicalGroup` at the actual two ranks.

The inputs are

```text
ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology,
ρ : Representation ℂ GL_(k+1)(F) V,
B : SmoothRep ℂ P_(r+2)(F).
```

The two carrier universes `uV,uW` are independent of each other and of
`uF`. Naturality permits independent target universes `uV',uW'`. The GL
representation is arbitrary; the actual source-Phi construction requires
`B` smooth. No admissibility, finite dimension, irreducibility, finite
length, genericity, chosen vector, canonical topology, universe saturation,
or assumed compatibility is added. Zero objects and full input carriers
are retained.

With Library convention `mirabolic n F.Carrier = P_(n+1)(F)`, set

```text
G = mirabolic (k+r+1) F.Carrier,
H = mirabolic (k+1+r) F.Carrier,
L = (leftStages k r F.Carrier 1).comap plusSuccessor ≤ G,
S = leftSubgroup (k+1) r F.Carrier ≤ H.
```

Both ambient groups realize `P_(k+r+2)` but their actual rank transport is
retained. The higher mixed product has GL input rank `k+1`, source rank
`P_(r+2)` and ambient rank `P_(k+r+3)`; its Phi-minus output has rank
`P_(k+r+2)`. The lower coefficient uses exactly
`phiMinus T ψ r : P_(r+2) → P_(r+1)`. No `P_0` or Phi-minus on `P_1`
is introduced.

`leftPhiLowerRankEquiv k r R : G ≃ₜ* H` is the inverse of
`MixedOrbit.rankCast (show k+1+r = k+r+1 by omega)`. Its continuity and
inverse continuity are the published entry-preserving rank-cast theorems.
It changes indices through `Fin.cast`, retaining every matrix entry.

`leftPhiLowerRank_mem_iff` proves

```text
h ∈ L ↔ leftPhiLowerRankEquiv k r R h ∈ S
```

for every `h : G`. It rewrites the published stages comap equality
`leftPhiStages_comap_section`, then applies
`mem_leftSection_one_iff`. This is equality of the actual subgroup
membership conditions, not just a containment or a coefficient-level map.

`leftPhiLowerSectionEquiv_eq` identifies the published
`leftPhiLowerSectionEquiv : L ≃* S` with restriction of the ambient rank
map. Subtype extensionality reduces this equality to the published stages
section value formula, carried through the inverse rank cast. Membership
proofs are retained in the resulting subtype.

## Full coefficient and compact-induction comparison

Write

```text
A = leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1,
Q = leftPhiNormalizedStagesQuotient T k r ρ B.representation ψ 1,
C = leftPhiSourceCoefficient T k r ψ ρ B,
E = leftPhiNormalizedSourceEquiv T k r ψ ρ B,
φ = leftPhiLowerRankEquiv k r F.Carrier.
```

Here `A` acts on the entire actual normalized identity-orbit quotient `Q`.
It includes the higher inducing covariance and the ambient inverse-half
determinant character. The full coefficient `C` is exactly the inducing
representation for the lower left mixed product: the actual lower positive
covariance twist of `ρ` tensored with the normalized source-Phi object.
Its carrier is `V ⊗[ℂ] ((Mirabolic.phiMinus T ψ r).obj B)`.
The published full linear equivalence underlying `E` sends

```text
[v ⊗ w] ↦ v ⊗ Mirabolic.phiMinusQuotient T ψ r B w.
```

`leftPhiNormalizedSourceEquiv_rank_action` proves for every `l : L` and
`z : Q`

```text
E (A l z) = C ⟨φ l, membership⟩ (E z).
```

The proof starts with the actual intertwining property of `E`, whose
target coefficient is pulled back along `leftPhiLowerSectionEquiv`.
It then transports the target action through
`leftPhiLowerSectionEquiv_eq` by `congrArg` and transitivity. Thus the
published full quotient action comparison is used on all quotient elements;
there is no new character identity or residual scalar left to assume.

The published `compactInducedTransport φ L S hS A C E hE` is an equivalence
from `(compactInduced S C).comp φ.toMonoidHom` to
`compactInduced L A`. Its inverse is `leftPhiCompactSourceEquiv`, so this
module proves exactly

```text
Representation.Equiv
  (compactInduced L A)
  ((compactInduced S C).comp φ.toMonoidHom).
```

Both sides use the actual `Induction.CompactFunctions`: covariant
functions, uniformly fixed on the right by an open subgroup, with compact
projected support. The published transport preserves covariance by the full
coefficient action equality, transports the open subgroup along the
continuous ambient equivalence, and transports compact projected support
through the continuous map on left quotients. Its inverse preserves the
same conditions in the other direction. Therefore the comparison is a
bijection on the entire compact-induced carriers, not a statement about
selected representative functions, a subspace, or only algebraic induction.
Right translation is intertwined by multiplicativity of the ambient rank
map.

The theorem `leftPhiCompactSourceEquiv_eval` records its evaluation formula:
for every actual compact function `a` and every `h : H`,

```text
(leftPhiCompactSourceEquiv ... a)(h) = E (a (φ.symm h)).
```

This formula follows definitionally from the inverse of the published
transport. It retains both the full normalized coefficient equivalence
and the actual forward rank cast in the argument of `a`.

## Naturality in the two actual inputs

Let `f : ρ.IntertwiningMap ρ'` and
`g : B.representation.IntertwiningMap B'.representation` be arbitrary,
with all four carrier universes independent. Set

```text
m = leftPhiNormalizedStagesMap T k r ρ B.representation ψ f g 1,
n = leftPhiSourceCoefficientMap T k r ψ ρ B f g.
```

The first is the actual map on the entire normalized stages quotient;
the second is the actual lower coefficient map, with underlying linear
map `f ⊗ phiMinus.map g`. For every actual compact function `a`,
`leftPhiCompactSourceEquiv_natural` proves

```text
leftPhiCompactSourceEquiv ... ρ' B' (compactInducedMap L m a)
  = compactInducedMap S n (leftPhiCompactSourceEquiv ... ρ B a).
```

The proof applies the three subtype extensionality principles for compact,
uniformly smooth, covariant functions and then function extensionality.
At each `h : H` the equation is precisely
`leftPhiNormalizedSourceEquiv_natural` at `a (φ.symm h)`.
The published transported source coefficient map has the same underlying
linear map as `n`. This proves naturality for all functions and both input
maps. It avoids the same-universe restriction of the older generic
transport-naturality theorem without changing that published theorem.

## Import and mathematical dependency audit

The two direct project imports are

```text
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
```

The full project closure contains 94 imported modules, excluding this
entry. All 188 imported Lean/Markdown files are nonempty, byte-identical to
the published Library, and verified against its manifest at commit
`31d47a6f0dabd6dff6c65e1b78f4821ddedc9bc8`. No pending module or peer draft
is imported. In particular the stages compact-induction and ambient
induction normalization units are not inputs.

The direct mathematical inputs are the published actual stages comap
identity, actual identity-section membership characterization, actual
section and continuous rank equivalences, the full normalized source
coefficient representation equivalence and its full naturality, and the
generic compact-induction transport. Transitively the source comparison
uses explicit matrix radical and determinant calculations, actual
character localization, tensor quotient and linear transport algebra,
the normalized source-minus construction and smooth pullback/twist
infrastructure. The generic compact-induction transport uses only the
published compact-function definitions, covariance, open subgroup comaps,
continuous quotient maps and compact images. Admissibility, irreducibility,
Noetherian and Whittaker infrastructure in the import closure supplies no
representation finiteness hypothesis or consumer conclusion.

| Condition | Actual dependency finding |
| --- | --- |
| Six host conclusions | The host statement and proof modules are absent. No mixed-minus compatibility or boundary conclusion supplies an input. This unit proves compact induction of the normalized identity coefficient with its actual rank pullback. |
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
| Separate owners and controls | This compact-induction unit does not duplicate the separate restriction-sequence or exactness work. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |
| Actual compact induction | Both complete covariant uniformly smooth compact-supported carriers are retained. Support transport and its inverse are proved in the published generic theorem. |
| Actual subgroup and rank map | The exact subgroup membership equivalence is proved for every ambient element. The continuous inverse rank cast is present in the target action and the evaluation formula. |

A scan of this module and its complete project closure finds no Lean-code
occurrence of the host's 38 excluded task identifiers or 24 named consumer
declarations, and no proof holes, new axioms or unsafe evaluation commands.
Excluded names in explanatory Markdown are audit prose. Development
compilation is separate from independent semantic acceptance and
publication.

## Complete project import closure

Every direct and transitive project import, excluding this entry, is
listed below. The authorized environment supplies unchanged Lean and
Mathlib, pinned respectively to commits
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and
`5ed2965256430c3649e86755f9576b54eca72435`.

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
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
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

The complete external import boundary of these project modules is listed
below; their transitive standard-library imports are supplied by the
pinned environment, not project-authored mathematical inputs.

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.Equiv.TypeTags
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Fin.Rev
Mathlib.Data.Matrix.Block
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Rep.Res
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```
