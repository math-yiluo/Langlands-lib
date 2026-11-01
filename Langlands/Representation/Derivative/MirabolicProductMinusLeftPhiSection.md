# Actual nested left-orbit quotient and section action

Author: Worker 499.

This module constructs `leftPhiStagesCoefficientEquiv` in
`Langlands.Derivative.MirabolicProductMinus`. It identifies the actual
nested stages coefficient quotient with localization at the whole actual
radical intersection, preserving every coefficient representative. It proves
the exact section-action formula, its identity-orbit external-tensor formula,
and naturality for arbitrary stabilizer intertwiners on independent carrier
universes. These are algebraic constructions toward BZ77 Proposition 4.13(b).
The compact-induction comparison, Haar ratio, normalized representation
comparison and final six-part host theorem remain separate obligations.

## Source and provenance

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472, registered as `bernstein-zelevinsky-1977-induced-i`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8, printed pp.444–445 (one-based PDF pages 5–6), supplies
character localization and its normalizing-subgroup action. Sections
3.1–3.2, printed pp.450–451 (PDF pages 11–12), define the positive
last-coordinate character and the minus functors. Section 4.12(II),
printed pp.456–457 (PDF pages 17–18), gives the left mixed subgroup;
§4.13(b), printed p.458 (PDF page 19), states the corresponding
functorial comparisons. Section 7.2, printed p.471 (PDF page 32),
gives the two orbit representatives. These passages and relevant page
images were read during this task. The bounded supplied-source and
public-note errata search found no applicable BZ77 entry; no global
absence is asserted.

The nested subgroup identifications, class-preserving quotient transport,
section formula and naturality proof are internal derived content. They use
the published actual matrix projection and successor, orbit stabilizers and
stages, radical character, quotient transport and section action. BZ77
motivates their p-adic specialization; it does not literally state these
arbitrary-commutative-ring adapters. No representation comparison from the
source or pending proof is assumed. Worker 499 wrote the construction;
no peer draft contributes a proof body.

## Parameters, actual groups and characters

The algebraic declarations quantify arbitrary `R : Type uR` with
`[CommRing R]` and arbitrary `k,r : ℕ`, including zero. The character
constructions take any `[TopologicalSpace R]` and the supplied
`ψ : UnitaryAdditiveCharacter R`, which already bundles continuity and
nontriviality. They require no topological-ring, local-compactness or
field hypothesis. `leftPhiInducingSection_tmul` is entirely algebraic.

The coefficient carriers `V : Type uV` and `W : Type uW` have arbitrary
additive-group and complex-module structures, with independent universes.
All representations and intertwiners are arbitrary. There is no smoothness,
admissibility, irreducibility, finite-dimension, finite-length, genericity,
nonzero-object, chosen-vector or universe-saturation assumption.

For clarity write

```text
G   = plusSubgroup (k+r+1) R,
L   = mirabolic (k+r+1) R,
p   = plusProjection : G ->* L,
s   = plusSuccessor : L ->* G,
P_i = leftStages k r R i,
H_i = leftStabilizer k r R i,
K_i = P_i.comap s,
H'_i = H_i.subgroupOf P_i.
```

Here `i : Fin 2` is arbitrary. The published representative `0` is the
descending cycle and `1` is the identity. The ambient group containing
`G` is `mirabolic (k+r+2) R = P_(k+r+3)(R)`, and
`L = P_(k+r+2)(R)`. The positive GL factor in the eventual host has
rank `k+1`. The source mirabolic factor for Phi-minus is
`mirabolic (r+1) R = P_(r+2)(R)`, whose output is `P_(r+1)(R)`.
Thus the host indexing `phiMinus T ψ r : P_(r+2) -> P_(r+1)` is
retained. This unit introduces neither `P_0` nor Phi-minus on `P_1`.

`plusKernelRadicalEquiv` identifies `ker p` with the actual
`radical (k+r+2) R`, using `projection_eq_one_iff` in one direction
and `plusRadical` in the other. Every map retains the original radical
matrix. `leftStages_contains_kernel` uses the published definition
`P_i = p⁻¹(leftSection k r R i)` and the subgroup's identity element.
It supplies exactly the kernel-containment premise for the restricted
split retraction

```text
p_i = leftPhiStagesRetraction k r i : P_i ->* K_i,
s_i = leftPhiStagesSection k r i : K_i ->* P_i.
```

The equality `p ∘ s = id` proves
`K_i = leftSection k r R i`. `leftPhiStagesSectionEquiv` is the
subgroup equivalence induced by this equality; its value is literally
the original element of `L`. Section containment is proved only for
`l : K_i`, which is the necessary restricted domain. There is no
stronger global assertion that every element of `s(L)` lies in `H_i`.
`leftPhiStagesInducingEquiv` removes the intermediate membership in
`P_i` from `H'_i`. The named inducing-section equality proves that
this removal carries the nested section to the published actual
`sectionInclusion` of the corresponding lower orbit section.

`leftPhiStagesKernelEquiv` removes intermediate stages membership
from `ker p_i` and then applies the actual kernel/radical equivalence.
The positive character is precisely

```text
Theta_i = theta ψ (k+r+1) ∘ leftPhiStagesKernelEquiv k r i.
```

There is no inverse character. `plusKernelTheta_sectionInvariant`
identifies inverse section conjugation with conjugation by the
actual successor of the inverse lower mirabolic element, then uses
`Mirabolic.theta_isInvariant`. That published proof is the last-row
matrix identity fixing the final radical coordinate. Restricting this
identity gives `leftPhiStagesTheta_sectionInvariant` with exactly the
restricted section domain above.

## Quotient equivalence and section formulas

Set

```text
N_i = kernelIntersection p_i H'_i,
I_i = leftRadicalIntersection k r R i,
phi_i = leftPhiStagesInducingEquiv k r i,
j_i = leftRadicalInclusion k r R i,
eta_i = intersectionCharacter p_i Theta_i H'_i,
theta_i = leftOrbitTheta k r ψ i.
```

`N_i` is a subgroup of the nested inducing group `H'_i`.
`leftPhiStagesIntersectionEquiv` switches the two membership proofs,
removes membership in the stages group, and replaces the ambient
projection kernel by the actual radical. Its result is exactly `I_i`;
the matrix is unchanged in both directions.

For any `σ : Representation ℂ H_i V`, the module constructs

```text
E_sigma = leftPhiStagesCoefficientEquiv k r ψ i σ :
  Coinvariants (sigma.comp phi_i) N_i eta_i
    ≃ₗ[ℂ]
  Coinvariants (sigma.comp j_i) top (theta_i.comp top.subtype).
```

The `top` on the right is the whole subgroup **inside `I_i`**. Thus
all elements of the actual radical intersection impose the relations
`sigma(j_i(u))v - theta_i(u) • v`; it is not a localization at a
trivial subgroup. `Jacquet.Localization.transportEquiv` is applied
to the actual intersection equivalence followed by `topEquiv.symm`,
and to `LinearEquiv.refl ℂ V`. Both action compatibility and character
compatibility are definitional equalities of the actual inclusions.
The two quotient descents in the published transport construction
supply inverse maps. The representative formula is

```text
E_sigma [v]_nested = [v]_actual.
```

`leftPhiStagesAction` is the published `subgroupAction` for
`p_i,s_i,Theta_i,H'_i` and the actual restricted representation.
`leftPhiStagesCoefficientEquiv_section_mk` proves

```text
E_sigma (leftPhiStagesAction k r ψ i sigma l [v]_nested)
  = [sigma(sectionInclusion (leftPhiStagesSectionEquiv k r i l)) v]_actual.
```

Its implemented proof composes the named `subgroupAction` class
formula, the class-preserving transport formula, and the actual
inducing-section equality using `congrArg` and equality transitivity.
It does not replace the quotient or discard an action.

For the identity orbit, take arbitrary

```text
rho : Representation ℂ GL_(k+1)(R) V,
tau : Representation ℂ P_(r+2)(R) W,
sigma = (external rho tau).comp (leftCoefficient k r R 1).
```

For `l : K_1`, let

```text
(a,q) = leftProjection
  (leftIdentitySectionEquiv k r R (leftPhiStagesSectionEquiv k r 1 l)).
```

The published `leftSectionCoefficient_one` gives the complete pair
`(a, successor q)`. `leftPhiInducingSection_tmul` applies the actual
external tensor action to this pair, and
`leftPhiStagesCoefficientEquiv_one_section_tmul` consequently proves

```text
E_sigma (leftPhiStagesAction k r ψ 1 sigma l [v tensor w]_nested)
  = [rho(a)v tensor tau(successor q)w]_actual.
```

Every `v,w` and every actual section element is retained. This formula
is unnormalized. No Haar character, determinant twist or normalized
source Phi-minus action has been suppressed.

## Naturality and implemented proof

`leftPhiStagesMap` is exactly `subgroupMap` applied to
`restrictAlongMap phi_i f` for an arbitrary stabilizer intertwiner
`f : sigma.IntertwiningMap tau`. Its formula on classes is
`[v]_nested -> [f(v)]_nested`. The equivalences are defined for each
representation before any intertwiner is chosen.

`leftPhiStagesCoefficientEquiv_natural` quantifies arbitrary source
and target carrier universes and every localized element `z`. It proves

```text
E_tau (leftPhiStagesMap k r ψ i f z)
  = mapLinear top (theta_i.comp top.subtype)
      (restrictAlongMap j_i f) (E_sigma z).
```

The proof uses `Submodule.Quotient.induction_on` to reduce to each
coefficient representative, then composes the subgroup-map class
formula with the transport class formula. The right-hand class map
has exactly the same representative. Instantiating `f` with the
published external tensor intertwiner permits arbitrary intertwiners
in both external factors, with independently universe-valued input
and output carriers. No finite-dimensional argument or basis is used.

## Import and mathematical dependency audit

The seven direct project imports are `MirabolicMixedOrbitCharacters`,
`MirabolicMixedOrbitStages`, `MirabolicMixedOrbitSectionCoefficients`,
`SplitStagesRetraction`, `SplitKernelLocalizationData`,
`SplitQuotientStatement` and `MixedProducts`, with their full names
in the closure below. The complete closure has 75 project modules.
Every imported Lean/Markdown pair is nonempty, unchanged and
byte-identical to the published Library and manifest at commit
`4c821aa88a155b2bb027aa516770ffd74d5635aa` (150 checked files).
This module imports neither `MirabolicProductMinusLeftPhiCoefficient`
nor `MirabolicProductMinusLeftPhiNormalization`, and imports no generic
character-stages statement or comparison proof.

The actual mathematical inputs are the explicit plus-projection and
successor homomorphisms and split identity, the kernel characterization
by the actual radical, the left stages and stabilizer inclusions,
restricted split-retraction membership maps, the positive character's
last-coordinate invariance, actual section coefficient pair,
character-quotient transport, subgroup action and map formulas,
restriction of intertwiners, and external tensor action. Their proofs
reduce to subgroup membership, actual matrix entries, relation spans,
quotient descent and elementary linear algebra. The ordinary
split-quotient proof supplies the restricted retraction construction;
no character compact-induction comparison is inferred from it.

The broader induction, smoothness, category, filtration and tensor
imports supply definitions and algebraic interfaces. In particular
`Tensor.Finite` supplies tensor infrastructure, and the Whittaker
modules supply algebraic character infrastructure. No finiteness,
classification, normalized comparison or consumer conclusion is used.
A Prop-valued target definition is not a theorem premise.

The following audit covers both direct and transitive mathematical inputs.

| Condition | Actual dependency finding |
| --- | --- |
| Six host mixed-minus conclusions | No host conclusion or proof is imported. Only the nested coefficient transport, actual unnormalized section formulas and naturality are constructed. The final natural isomorphisms, exact sequence and conjunction remain obligations. |
| Plus functors, adjunction, BZ77 §4.13(d) | No plus functor, adjunction or submodule-detection conclusion supplies an input. The elementary matrix subgroup `plusSubgroup` and its projection/section are the permitted actual group maps. |
| General Leibniz and derivative formulas | No general Leibniz proof, segment derivative formula, Ze80 §3.5 or §9.6 formula, or unproved BZ77 derivative result supplies an input. The positive radical character is an explicit matrix construction. |
| Segment head, socle and Jacquet formulas | No individual special-head or segment-socle existence, linked/unlinked or juxtaposed reverse-product conclusion, quotient homomorphism, or full/head/socle/special Jacquet formula supplies an input. |
| Product, commutation and gluing consumers | No segment product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, or Ze80 4.2 or 9.7 criterion is used. |
| Special-head criterion and generic uniqueness | Neither the special-head product criterion nor generic segment-product uniqueness is used. |
| Ordered existence and exhaustion | No ordered multisegment-socle existence, socle or special-head exhaustion, ordered strong-head existence, quotient coverage or ordered conversion supplies an input. |
| Analytic, tempered, square-integrable conclusions | No segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable classification or exhaustion, regular exhaustion, or Ze80 9.3 assertion supplies an input. |
| Two-supercuspidal consumers | Neither nonadjacent product irreducibility, product structure nor its full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) supplies an input. |
| Supercuspidal and single-block finiteness | No supercuspidal coinvariant-finiteness statement, all-character single-block conclusion, arbitrary-character finiteness theorem or consequence supplies an input. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal finiteness conclusion, consequence or prohibited mirabolic finite-length route supplies an input. |
| Generality | All natural k,r including zero, the supplied character/topology and independent ring and carrier universes are retained. The complete coefficient representation and actual intersection are used. There is no chosen unit vector, finite-dimensional, admissible, finite-length, generic, nonzero-object or theorem-valued premise. |
| Published inputs and target preservation | Every imported pair is unchanged and public. Pending statements, drafts, source formulas and citations are not theorem premises. No host statement or its imported pair is modified. |
| Separate owners and user controls | This focused construction does not duplicate a restriction sequence, exactness proof or generic compact-induction comparison. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and all current suspensions remain binding; no peer message waives them. |

A source scan of this entry and its complete project closure finds no
occurrence in Lean code of the host's 38 excluded task identifiers
or 24 named consumer declarations, and no proof holes, new axioms or
unsafe evaluation commands. This supplements the mathematical dependency
audit above. Compilation and declaration inspection are development
checks; independent acceptance and publication remain required.

## Complete project import closure

Both direct roots and all their transitive project imports are included,
excluding the present module. Mathlib is supplied by the pinned environment
and remains unchanged.

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
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
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
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
