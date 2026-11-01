# Actual normalized left-Phi stages coefficients

Author: Worker 499.

This module constructs `leftPhiNormalizedStagesTensorEquiv` in
`Langlands.Derivative.MirabolicProductMinus`. It identifies the entire
actual normalized identity-orbit coefficient quotient with the GL factor
tensored with the actual positive-character source quotient. The
identification is natural in both inputs. The module also computes the
ambient-normalized section action and proves that the complete cycle
coefficient quotient is subsingleton. These are lower coefficient results
for BZ77 §4.13(b); a representation equivalence with the normalized source
Phi coefficient, compact-induction comparison and the six-part host
compatibility theorem remain separate obligations.

## Source and provenance

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472, registered as `bernstein-zelevinsky-1977-induced-i`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b), printed pp.444–445 (one-based PDF pages 5–6), defines
positive-character localization with inverse-half normalization of the
normalizing action. Sections 3.1–3.2, printed pp.450–451 (PDF pages
11–12), specify the mirabolic groups, positive last-coordinate character
and minus functors. Section 4.12(II), printed pp.456–457 (PDF pages
17–18), specifies the upper-block left mixed product; §4.13(b), printed
p.458 (PDF page 19), states its functorial comparison. Section 7.2,
printed p.471 (PDF page 32), gives the identity and cycle representatives.
These passages and relevant page images were read during this task. The
bounded supplied-source and public-note errata search found no applicable
BZ77 entry; no global absence is asserted.

The present normalized stabilizer, quotient identifications, action
calculation and naturality proofs are internal derived content. They use
the published actual section and radical coefficient constructions,
localization transports and determinant-character calculation. No source
representation comparison is assumed. The only direct imports are the
published `MirabolicProductMinusLeftPhiSection`,
`MirabolicProductMinusLeftPhiCoefficient` and
`MirabolicProductMinusLeftPhiNormalization` modules. The source-action,
Haar and generic character-stages comparison modules are not imported.
Worker 499 wrote this construction; no peer draft supplies a proof body.

## Parameters, ranks and actual quotient

The declarations quantify arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}`, supplied `T : F.TopologicalData`, and all
`k,r : ℕ`, including zero. Every required topology is `T.topology`,
installed in exported types and definition bodies. The character
`ψ : UnitaryAdditiveCharacter F.Carrier` uses this topology; continuity
and nontriviality are bundled. The inputs are arbitrary representations

```text
ρ : Representation ℂ GL_(k+1)(F) V,
τ : Representation ℂ P_(r+2)(F) W.
```

Neither representation is required to be smooth in this algebraic
coefficient unit. The field universe `uF` and carrier universes `uV,uW`
are independent. Naturality permits independent target carrier universes
`uV',uW'` as well. There is no finite dimension, admissibility,
irreducibility, finite length, genericity, nonzero vector, chosen basis,
canonical topology, universe saturation or theorem-valued premise.
Zero objects are included.

Write `K=k+1`. The higher left mixed product is on `P_(k+r+3)`;
ambient Phi-minus has output group `P_(k+r+2)`. The indexing convention
is `mirabolic n F.Carrier = P_(n+1)(F)` and
`phiMinus T ψ r : P_(r+2) → P_(r+1)`. No `P_0` is introduced and
Phi-minus is not applied to `P_1`.

For `i : Fin 2`, let `S_i = leftStabilizer k r F.Carrier i` be the
actual orbit stabilizer and `D_i = leftRadicalIntersection k r F.Carrier i`
its actual radical intersection. Index `0` is the cycle and index `1`
is the identity. Let `c_i = leftCoefficient k r F.Carrier i` and
`λ = T.leftLeviCharacter (k+1) (r+1)`. The new stabilizer character and
representation are exactly

```text
χ_i = λ ∘ c_i,
σ_i = twist χ_i ((external ρ τ).comp c_i).
```

These are `leftPhiStabilizerCharacter` and
`leftPhiNormalizedStabilizer`. They retain the entire actual covariance.
The nested quotient `Q_i = leftPhiNormalizedStagesQuotient ... i` is

```text
Coinvariants (leftPhiStagesRepresentation k r i σ_i)
  (leftPhiStagesIntersection k r i)
  (intersectionCharacter (leftPhiStagesRetraction k r i)
    (leftPhiStagesTheta k r ψ i) (leftPhiStagesStabilizer k r i)).
```

Thus its relation group is the actual stabilizer intersection inside the
actual stages kernel. It is neither a trivial-subgroup quotient nor a
selected set of tensor relations. Its carrier is a quotient of the full
`V ⊗[ℂ] W`.

## Removing covariance on the entire radical

The private `leftPhi_radical_determinantNorm` uses the actual inclusion
of the mirabolic radical into the upper-unipotent group. The determinant
of its upper-triangular matrix is the product of its diagonal ones.
Unit extensionality and the supplied multiplicative normalized absolute
value therefore give determinant norm one.

The published radical coefficient formula is `(1, source(u))`, where
`source(u)` is an actual source radical element. Evaluating the complete
higher covariance at this pair and using its determinant norm one proves
`leftPhiStabilizerCharacter_radical` for every element of `D_i`, at both
representatives. Consequently `leftPhiNormalizedStabilizer_radical`
identifies the restricted normalized action with the actual unnormalized
radical coefficient action on every tensor vector.

`leftPhiNormalizedRadicalEquiv` applies `transportEquiv` with identity
group transport and identity linear equivalence. The action equality just
proved makes it an equivalence of the full relation quotients. It sends
every class `[x]` to the actual unnormalized orbit class of `x`.
`leftPhiNormalizedStagesCoefficientEquiv` composes the published actual
stages-intersection equivalence with this transport. Its representative
formula is again `[x] ↦ leftPhiCoefficientMk ... i x`. This proves an
identification on all quotient classes with no dimension hypothesis.

## Actual section action and rank transport

On the smaller stages section
`L_i = (leftStages k r F.Carrier i).comap plusSuccessor`, define

```text
β_i = phiMinusCharacter T (k+r+1) ∘ L_i.subtype,
A_i = twist β_i (leftPhiStagesAction k r ψ i σ_i).
```

These are `leftPhiAmbientSectionCharacter` and
`leftPhiNormalizedStagesAction`. The twist is the actual ambient
inverse-half determinant normalization. If `l ∈ L_i` and `j_i(l)` is
its actual `sectionInclusion` after `leftPhiStagesSectionEquiv`, then
`leftPhiNormalizedStagesCoefficientEquiv_action_mk` proves

```text
E_i(A_i(l)[x]) = (β_i(l) χ_i(j_i(l)) : ℂ) •
  leftPhiCoefficientMk ... i (((external ρ τ).comp c_i) (j_i(l)) x).
```

The proof moves the ambient scalar through the linear equivalence,
uses the published actual section action on representatives, and then
moves the covariance scalar through the quotient map. Multiplication
of unit values and `smul_smul` combine the two scalars. No scalar is
suppressed.

At index `1`, put

```text
h(l) = leftIdentitySectionEquiv k r F.Carrier
         (leftPhiStagesSectionEquiv k r 1 l)
       ∈ leftSubgroup (k+1) r F.Carrier,
(a,q) = leftProjection h(l).
```

The actual identity-section equivalence contains the inverse rank cast
along `k+1+r = k+r+1`. The theorem `leftPhiCharacter_rankCast_symm`
proves invariance of the inverse-half character under this cast for an
arbitrary equality of ranks: equality induction reduces the cast to its
identity matrix, checked by subgroup, unit and matrix extensionality.
Using the published value formulas of both actual section equivalences,
`leftPhiNormalizedSection_scalar` then proves the equality in `ℂˣ`

```text
β_1(l) χ_1(j_1(l)) = leftPhiSectionCharacter T (k+1) r (h(l)).
```

The right side is the published complete section character, including
ambient inverse-half normalization and higher covariance at
`(a, successor q)`. The actual section coefficient formula proves
`leftPhiNormalizedStagesCoefficientEquiv_one_tmul`: the vector is
`ρ(a)v ⊗ τ(successor q)w`, with exactly this full scalar. Every rank
transport is retained in `h(l)`.

## Full tensor identification and cycle vanishing

Compose `leftPhiNormalizedStagesCoefficientEquiv ... 1` with the
published `leftPhiTensorEquiv`. This defines
`leftPhiNormalizedStagesTensorEquiv : Q_1 ≃ₗ[ℂ] V ⊗[ℂ] Q_τ`, where

```text
Q_τ = Coinvariants τ (radical (r+1) F.Carrier) (Mirabolic.theta ψ r).
```

The source character is the positive final-coordinate character.
The formula `leftPhiNormalizedStagesTensorEquiv_mk_tmul` sends
`[v ⊗ w]` to `v ⊗ [w]`. The action formula
`leftPhiNormalizedStagesTensorEquiv_action_tmul` applies the tensor
equivalence to the preceding section calculation and obtains

```text
E(A_1(l)[v ⊗ w]) = (leftPhiSectionCharacter T (k+1) r (h(l)) : ℂ) •
  (ρ(a)v ⊗ [τ(successor q)w]).
```

This is an equality on every generating pure-tensor class, and the linear
equivalence is defined on the entire quotient. This module does not yet
package it as a representation equivalence with the normalized source
Phi-minus coefficient.

`leftPhiNormalizedStagesQuotient_zero_subsingleton` transfers the
published vanishing of the complete cycle coefficient quotient through
the injective `leftPhiNormalizedStagesCoefficientEquiv ... 0`. The
published vanishing uses nontriviality of the source character. The
conclusion here is subsingleton for the full normalized cycle quotient,
without a nonzero input assumption.

## Naturality on full quotients

For arbitrary `f : ρ.IntertwiningMap ρ'` and
`g : τ.IntertwiningMap τ'`, `leftPhiNormalizedStabilizerMap` pulls back
the external tensor intertwiner along `c_i` and twists it by `χ_i`.
`leftPhiNormalizedStagesMap` applies the published actual stages map
and twists by `β_i`. These are actual intertwiners; the latter sends
`[x]` to `[TensorProduct.map f.toLinearMap g.toLinearMap x]`.

`leftPhiNormalizedStagesCoefficientEquiv_natural` proves commutation
with the actual `leftPhiCoefficientMap` on every quotient element.
Quotient induction reduces the equality to representatives, where both
sides preserve precisely the class of the tensor map.
Finally `leftPhiNormalizedStagesTensorEquiv_natural` composes this
naturality with that of the published tensor equivalence. On every
`z ∈ Q_1` it proves

```text
E'(leftPhiNormalizedStagesMap f g 1 z)
  = TensorProduct.map f.toLinearMap
      (mapLinear (radical (r+1) F.Carrier) (Mirabolic.theta ψ r) g) (E z).
```

All four carrier universes remain independent. No finite basis or chosen
quotient representatives are needed. Definition inspection of the stages
map and theorem inspection of the tensor naturality each report
`uF,uV,uW,uV',uW'` and only `propext`, `Classical.choice`, `Quot.sound`.

## Import and mathematical dependency audit

The complete direct and transitive project import closure contains 90
modules, listed below. All 180 imported Lean/Markdown files are nonempty,
byte-for-byte identical to the published Library at commit
`f731c98e996e50a63c6431bd18cbbe3298a87530`, and verified against its manifest.
The present module is excluded from that count.

The actual mathematical inputs are the published entire radical and
stages coefficient equivalences, quotient representative and section
action formulas, complete identity-orbit tensor equivalence and its
naturality, cycle coefficient vanishing, actual matrix coefficient and
rank-transport formulas, and explicit determinant-normalized characters.
Transitively these use elementary matrix radicals and block calculations,
positive-character relation quotients, localization transport, tensor
linear algebra and real-power arithmetic. The new proof adds covariance
removal on the whole radical and retains the ambient scalar through the
actual rank cast. Imported smoothness, induction and category
infrastructure provide no representation-comparison conclusion.
Whittaker modules in the closure provide algebraic group and character
infrastructure, without any coinvariant-finiteness theorem.

The following audit covers every inherited exclusion directly and
transitively.

| Condition | Actual dependency finding |
| --- | --- |
| Six host conclusions | The host statement and proof modules are absent from the closure. No mixed-minus comparison or boundary conclusion supplies an input. The cycle coefficient vanishing is a lower quotient result, not any of the six host clauses. |
| Plus functors, adjunction and §4.13(d) | None supplies an input. The successor and actual radical subgroup are elementary matrix constructions. |
| General Leibniz and derivative formulas | No Leibniz theorem, unproved BZ77 comparison, Ze80 §3.5 or §9.6 formula, or segment derivative formula is used. The actual minus character definitions are published; no derivative comparison is a premise. |
| Individual head and socle existence | Neither individual special-head/reverse-socle nor segment-socle/reverse-head existence supplies an input. |
| Linked and unlinked segment conclusions | No unlinked irreducibility, linked reverse-product structure, pair reducibility, juxtaposed reverse-product structure or reverse-product quotient homomorphism is used. |
| Segment products, commutation and gluing | No segment-socle product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, Ze80 4.2 or 9.7 criterion, or consequence is used. |
| Segment Jacquet formulas | No full, head, socle or special-exponent Jacquet formula, its successor, or its downstream conclusion supplies an input. |
| Special-head criterion and generic uniqueness | Neither special-head product irreducibility nor generic segment-product uniqueness is used. |
| Ordered existence, coverage and exhaustion | No ordered multisegment-socle or strong-head existence, socle or special-head exhaustion, quotient coverage or ordered conversion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable Langlands classification, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. |
| Two-supercuspidal consumers | Neither nonadjacent-product irreducibility, two-supercuspidal product structure nor its full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) is used. |
| Supercuspidal and all-character finiteness | No supercuspidal, all-character single-block or arbitrary-character coinvariant-finiteness theorem or downstream consequence is used. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion or prohibited mirabolic finite-length route supplies an input. |
| Generality and normalization | All `k,r`, arbitrary supplied `T`, positive GL input rank and entire tensor factors are retained. There is no finite dimension, admissibility, irreducibility, finite length, genericity, chosen vector, universe saturation, canonical topology or theorem-valued premise. The ambient inverse-half scalar and higher covariance are computed through the actual rank cast, with no residual scalar. |
| Published-input requirement | Every imported pair is published and unchanged. Prop-valued statement definitions, source formulas, drafts, pending constructions and consumer tasks provide no unproved comparison premise. |
| Separate owners and controls | The unit computes actual normalized stages coefficients; it does not duplicate restriction-sequence or exactness work. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |

A source scan of this module and its entire project closure finds no
occurrence in Lean code of the host's 38 excluded task identifiers or
24 named consumer declarations, and no proof holes, new axioms or unsafe
evaluation commands. Excluded names in explanatory Markdown are audit
prose. Development compilation and declaration inspection do not supply
independent semantic acceptance or publication.

## Complete project import closure

The following list contains every direct and transitive project import,
excluding this new entry module. Mathlib is supplied by the pinned
approved environment; no Mathlib source is modified.

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
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
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
