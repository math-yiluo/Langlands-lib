# Actual Phi-minus as positive kernel localization

Author: Worker 499.

This module constructs `phiMinusKernelIso` and
`phiMinusNormalizedKernelIso` in
`Langlands.Derivative.MirabolicProductMinus`. These are natural
isomorphisms from elementary positive-character kernel localization, with
its actual successor section action, to the published unnormalized and
normalized Phi-minus functors. The normalized comparison retains the
complete inverse-half determinant character. The module also gives the
actual equivariant linear equivalences, their quotient-class formulas,
smoothness and naturality across independent coefficient universes.

This is a focused prerequisite for the mixed-product minus task. It does
not establish a mixed-product comparison, an orbit-localization theorem,
a short exact sequence, or the six-part host proposition.

## Source and provenance

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472, registered as `bernstein-zelevinsky-1977-induced-i`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b), printed pp.444–445 (one-based PDF pages 5–6), supplies
character localization with its normalizing action and inverse-half
normalization. Sections 3.1–3.2, printed pp.450–451 (PDF pages 11–12),
define the positive radical character and the minus functors. Section
4.13(b), printed p.458 (PDF page 19), is the eventual mixed-product
compatibility target. These passages and their relevant page images were
read during this task. The bounded supplied-source and public-note errata
search found no applicable BZ77 entry; this does not assert global absence.

The present comparison is internal derived content. The actual
plus-projection kernel is the actual radical with one additional subgroup
membership proof. The published `plusKernelRadicalEquiv` removes that
membership while preserving the ambient matrix. The published algebraic
`Jacquet.Localization.transportEquiv`, with the identity coefficient
equivalence, transports the full character quotient. Quotient induction
then verifies the successor action and every induced map. Finally the
published twist equivalence and twist functor retain exactly the prescribed
normalization. BZ77 motivates these objects; no source theorem or
unproved mixed-product conclusion supplies the comparison. Worker 499
wrote this construction, without a reused peer draft.

## Parameters, groups and full quotient carriers

All declarations use arbitrary `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p`, the supplied `T : F.TopologicalData`, and
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`. The character
already bundles continuity and nontriviality. The topology is introduced
by `letI := T.topology`; no canonical replacement topology is chosen.
The index `n : ℕ` is arbitrary, including zero. Source and target are

```text
mirabolic (n+1) F.Carrier = P_(n+2)(F),
mirabolic n F.Carrier     = P_(n+1)(F).
```

Thus `Mirabolic.phiMinus T ψ n` retains the shift
`P_(n+2) -> P_(n+1)`. At `n=0` it maps `P_2` to `P_1`; there is
no `P_0` and no application of Phi-minus to `P_1`.

Write

```text
G = mirabolic (n+1) F.Carrier,
Q = plusSubgroup n F.Carrier,
L = mirabolic n F.Carrier,
r = plusProjection : Q ->* L,
s = plusSuccessor : L ->* Q,
N = radical (n+1) F.Carrier,
e = plusKernelRadicalEquiv n : ker r ≃* N,
Theta = plusKernelTheta ψ n = theta ψ n ∘ e.
```

Here `plusSubgroup`, `plusProjection` and `plusSuccessor` are elementary
matrix group constructions. They are not plus representation functors.
The positive character has no inversion. Its invariance under inverse
section conjugation is the published
`plusKernelTheta_sectionInvariant`, proved from the last-coordinate
radical character and the actual successor matrix.

For any `ρ : Representation ℂ G V`, `phiMinusKernelAction` is exactly
`localizedAction r s Theta ... (ρ.comp Q.subtype)` on the entire carrier

```text
C_rho = Jacquet.Localization.Coinvariants (rho.comp Q.subtype) (ker r) Theta.
```

The quotient relations are all
`rho(u)v - Theta(u) • v`, for every `u : ker r` and `v : V`.
The action is the actual section action
`l [v] = [rho(successor l)v]`. `phiMinusKernelMap` restricts an arbitrary
ambient intertwiner along `Q.subtype` and applies the published
`sectionMap`, so its value on every class is `[v] -> [f(v)]`.

The algebraic action, map and smoothness declarations have arbitrary
additive-group complex-module carriers. The equivalences use arbitrary
smooth source objects. Every source and target coefficient universe in
the two naturality theorems is independent (`uV,uW`), and the bundled
functors are constructed for every `uV` independently of `uF`.
There is no admissibility, irreducibility, finite dimension, finite length,
genericity, nonzero-object, chosen-vector or universe-saturation premise.

## Implemented equivalences, actions and smoothness

`phiMinusKernelEquiv T ψ n A` applies the already published
`Jacquet.Localization.transportEquiv` to the representations
`A.representation.comp Q.subtype` and `A.representation`, localizing
subgroups `ker r` and `N`, positive characters `Theta` and
`T.mirabolicTheta ψ n`, subgroup equivalence `e`, and coefficient
equivalence `LinearEquiv.refl ℂ A`. Both compatibility premises are
reflexivity: the ambient matrix and positive character are unchanged.
The transport construction descends forward and backward linear maps
through the actual relation submodules and proves their inverse laws on
every quotient representative.

The resulting linear equivalence is packaged as a
`Representation.Equiv` with target
`((Mirabolic.phiMinusUnnormalized T ψ n).obj A).representation`.
The implemented equivariance proof uses linear-map extensionality followed
by `Submodule.Quotient.induction_on`. On each representative, both sides
are definitionally the class of `A.representation (successor l) v`.
Consequently the comparison identifies the complete actions, rather than
only the underlying modules. Its explicit formula is

```text
phiMinusKernelEquiv T ψ n A [v]_kernel
  = Mirabolic.phiMinusQuotient T ψ n A v.
```

`phiMinusKernelAction_smooth` first restricts the original smooth action
along the continuous subgroup inclusion. It then applies the published
`isSmooth_sectionAction` to the continuous actual successor section.
That theorem uses smoothness under continuous pullback and the actual
surjective quotient map; it assumes no exactness or finite-length theorem.

`phiMinusNormalizedKernelEquiv` applies `twistEquiv` to the entire
preceding equivariant equivalence with

```text
chi = Mirabolic.phiMinusCharacter T n
    = |det|^(-1/2) on P_(n+1).
```

The source action is `twist chi (phiMinusKernelAction ... )` and the
target is the actual `Mirabolic.phiMinus`, whose published definition is
unnormalized Phi-minus followed by the same smooth twist. The underlying
linear equivalence and its formula on all classes remain unchanged.
No determinant or residual scalar factor is suppressed.

## Naturality and functor packaging

For arbitrary smooth objects `A,B`, arbitrary ambient intertwiner `f`
across independent carrier universes, and every `z : C_A`,
`phiMinusKernelEquiv_natural` proves

```text
E_B (phiMinusKernelMap T ψ n f z)
  = Jacquet.Localization.mapLinear N (T.mirabolicTheta ψ n) f (E_A z).
```

Its proof is quotient induction: both sides on `[v]` are the actual
radical class `[f(v)]`. The normalized naturality theorem has the
complete twisted source map and normalized equivalences and uses exactly
this same equality; twisting does not change the underlying linear map.
This statement applies in particular to every external tensor
intertwiner when the bridge is used for a mixed product.

`phiMinusKernelFunctor` sends every smooth ambient representation to the
proved smooth kernel action, and every smooth morphism to the actual
kernel map. The implemented identity and composition proofs use
pointwise extensionality in the full smooth subcategory, then quotient
induction, where the laws are reflexive. `phiMinusKernelIso` packages
`SmoothRep.mkIso (phiMinusKernelEquiv ...)` using
`NatIso.ofComponents`; naturality is the full preceding equality.
`phiMinusNormalizedKernelIso` is `Functor.isoWhiskerRight` of that
natural isomorphism with the actual smooth determinant twist functor.
Its right endpoint is definitionally `Mirabolic.phiMinus T ψ n`.

## Import and mathematical dependency audit

The only direct imports are
`Langlands.Representation.Derivative.MirabolicMinus` and
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection`.
The full closure below contains 87 project modules. All 174 imported
Lean/Markdown files are nonempty, unchanged and byte-identical to the
published Library and manifest at commit
`1741653e5f4f861282ff64d062269adbcc65c686`. No pending candidate is imported.

The actual mathematical inputs are the elementary plus kernel/radical
equivalence and positive-character section invariance; quotient transport,
section actions and induced class maps; smooth continuous pullback and
surjective descent; actual minus-functor definitions; algebraic twisting
and the open kernel of the inverse-half determinant character; and
ordinary category extensionality, component isomorphisms and whiskering.
The relevant proofs reduce to subgroup membership, actual matrix entries,
relation spans, quotient descent and elementary linear algebra. The
imported tensor, admissibility, induction and Whittaker modules provide
infrastructure; no admissibility, tensor finiteness, general induction
comparison, Whittaker finiteness or consumer conclusion proves a step.
In particular `MirabolicPhiMinusMackey` and `MirabolicPlus` are absent
from the import closure.

The following conditions apply both directly and transitively.

| Condition | Actual dependency finding |
| --- | --- |
| Six host mixed-minus conclusions | No mixed-product comparison or exact sequence is a proof input. This module proves only the actual Phi-minus kernel-model comparison. The complete host theorem remains open. |
| Plus functors, adjunction and BZ77 §4.13(d) | No plus representation functor, adjunction or submodule-detection conclusion is used. The elementary matrix subgroup, projection and successor are the permitted actual group constructions. |
| General Leibniz and derivative formulas | No general Leibniz proof, segment derivative formula, Ze80 §3.5 or §9.6 formula, or unproved BZ77 derivative result is used. |
| Segment existence and Jacquet consumers | No individual special-head/reverse-socle or segment-socle/reverse-head existence, linked/unlinked or juxtaposed reverse-product structure, linked-pair reducibility or quotient homomorphism, or full/head/socle/special Jacquet formula supplies an input. |
| Product, commutation and gluing consumers | No segment product irreducibility, adjacent socle swap, two-segment commutation, linked gluing, or Ze80 4.2 or 9.7 criterion is used. |
| Special-head criterion and generic uniqueness | Neither the special-head product criterion nor generic segment-product uniqueness is used. |
| Ordered existence and exhaustion | No ordered multisegment-socle or strong-head existence, socle or special-head exhaustion, quotient coverage or ordered conversion supplies an input. |
| Analytic, tempered and square-integrable consumers | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable classification or exhaustion, regular exhaustion, or Ze80 9.3 assertion is used. |
| Two-supercuspidal consumers | Neither nonadjacent product irreducibility, product structure nor its full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) supplies an input. |
| Supercuspidal and single-block finiteness | No supercuspidal coinvariant-finiteness statement, all-character single-block conclusion, arbitrary-character finiteness theorem or downstream consequence supplies an input. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion, consequence or prohibited mirabolic finite-length route is used. |
| Generality and conventions | All natural n including zero, arbitrary supplied T and ψ, arbitrary smooth objects and independent field/carrier universes remain. Both the full positive quotient and actual inverse-half twist are retained. No P_0 is introduced. |
| Published inputs and target preservation | Every imported pair is unchanged and public. Prop-valued statement definitions, citations, drafts and pending proofs are not theorem premises. The exact host statement and its imports are untouched. |
| Ownership and user controls | This unit does not duplicate a restriction-sequence, exactness or general compact-induction comparison task. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and all current suspensions remain binding. No suspended worker is contacted to execute work. |

A source scan of this entry and the complete project closure finds no Lean
code occurrence of the host's 38 excluded task identifiers or 24 named
consumer declarations, and no proof holes, new axioms or unsafe evaluation
commands. This supplements the mathematical audit; mere absence of names
is not the independence argument. Compilation and declaration inspection
are development checks. Independent semantic acceptance and publication
are still required.

## Complete project import closure

This lists both direct roots and all their transitive project imports,
excluding the present module. The pinned environment supplies Mathlib.

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
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
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
