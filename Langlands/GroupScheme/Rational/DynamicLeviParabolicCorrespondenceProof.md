# Actual parabolics in a represented dynamic Levi: proof

Authors: Worker 4029 and Worker 15. Worker 15 recorded and compile-checked
the composite term in the public note
[`notes/group-schemes/smooth-split-torus-conjugacy-route.md`](../../../notes/group-schemes/smooth-split-torus-conjugacy-route.md)
(table "Targets that also use `PD`"). Worker 4029 put it into this module,
checked it again against the current Library and wrote this description.

`Langlands.GroupScheme.dynamicLeviParabolicCorrespondence` proves the exact
published proposition
`Langlands.GroupScheme.DynamicLeviParabolicCorrespondenceStatement.{u}`
(module `Langlands.GroupScheme.Rational.DynamicLeviParabolicCorrespondenceStatement`)
at an arbitrary universe `u`. The theorem has no hypotheses: its type is the
published proposition itself.

## What is proved

Let `k : Type u` be any field and `G` a connected reductive group scheme over
`Spec k`. Let `χ : Gm ⟶ G` be any cocharacter, and `j : L ⟶ G` any closed
subgroup that represents the actual dynamic centralizer
`Dynamic.centralizer χ` (witness `hj`). Then there is an order isomorphism

`e : ParabolicFunctor L ≃o ParabolicFunctorBelow (Dynamic.parabolic χ)`

with, for every actual parabolic subgroup functor `F` of `L`,
`(e F).val = Dynamic.extendFromCentralizer χ j hj F.val`, and, for every actual
parabolic subgroup functor `Q` of `G` contained in `Dynamic.parabolic χ`,
`(e.symm Q).val = Q.val.comap j`.

Both equalities are equalities of subgroup functors on all schemes over
`Spec k`, including nonreduced and non-affine test schemes. The forward value
is the exact pointwise product `j(F) U(χ)`; the inverse value is the inverse
image along `j`. The field may be finite or infinite, perfect or imperfect,
of any characteristic. Neither splitness of `G`, reductivity of `L`, nor any
structural correspondence is assumed; these are all supplied by the proved
inputs below. No quotient of rational-point groups and no topology enters.

## The Lean proof

The proof is a single application of the published conditional reduction
`dynamicLeviParabolicCorrespondenceStatement_of_structural_statements`
(module [`Rational.DynamicLeviParabolicTransfer`](DynamicLeviParabolicTransfer.md)).
That reduction has type

`ParabolicDynamicStatement.{u} → DynamicCentralizerReductiveStatement.{u} →
DynamicLeviCocharacterRealizationStatement.{u} →
SmoothMaximalSplitTorusConjugacyStatement.{u} → DynamicConnectedStatement.{u} →
RelativeRootSignInclusionsStatement.{u} → RelativeRootNegationStatement.{u} →
DynamicLeviParabolicCorrespondenceStatement.{u}`.

Each premise is supplied by its published unconditional proof, all in the
namespace `Langlands.GroupScheme`:

| Premise | Proof | Module |
| --- | --- | --- |
| `ParabolicDynamicStatement` (Milne 25.1) | `parabolicDynamic` | [`Absolute.ParabolicDynamicProof`](../Absolute/ParabolicDynamicProof.md) |
| `DynamicCentralizerReductiveStatement` | `dynamicCentralizerReductive` | [`Dynamic.CentralizerReductiveProof`](../Dynamic/CentralizerReductiveProof.md) |
| `DynamicLeviCocharacterRealizationStatement` | `dynamicLeviCocharacterRealization` | [`Dynamic.LeviCocharacterRealizationProof`](../Dynamic/LeviCocharacterRealizationProof.md) |
| `SmoothMaximalSplitTorusConjugacyStatement` (CGP C.2.3) | `smoothMaximalSplitTorusConjugacy` | [`Rational.SmoothMaximalSplitTorusConjugacyProof`](SmoothMaximalSplitTorusConjugacyProof.md) |
| `DynamicConnectedStatement` | `dynamicConnected` | [`Dynamic.ConnectedProof`](../Dynamic/ConnectedProof.md) |
| `RelativeRootSignInclusionsStatement` | `relativeRootSignInclusions` | [`Rational.RelativeRootSignInclusionsProof`](RelativeRootSignInclusionsProof.md) |
| `RelativeRootNegationStatement` | `relativeRootNegation` | [`Rational.RelativeRootNegationProof`](RelativeRootNegationProof.md) |

All seven are taken at the same universe `u` as the target, so no universe
transport is needed.

For each instance, the reduction returns the order isomorphism
`Dynamic.extendFromCentralizerOrderIsoOfStructuralStatements`, built on Worker
1116's `Dynamic.extendFromCentralizerOrderIso` (module
[`Dynamic.LeviParabolicExtension`](../Dynamic/LeviParabolicExtension.md)), and
the two functor equalities hold by `rfl`. Its route, documented in the
transfer module, is:

- Forward parabolicity: `L` is connected reductive by
  `dynamicCentralizerReductive`; an actual parabolic `F` of `L` is `P(ν)` for a
  cocharacter `ν` of `L` by `parabolicDynamic`; and
  `dynamicLeviCocharacterRealization` gives an ambient cocharacter `ψ` with
  `P(ψ) = j(P(ν)) U(χ)`, which is an actual parabolic of `G`.
- Inverse parabolicity: an actual parabolic `Q ≤ P(χ)` of `G` is `P(ψ)`. After
  conjugating `χ` into a maximal split torus containing the image of `ψ`
  (`smoothMaximalSplitTorusConjugacy`, `dynamicConnected` and the proved
  `dynamicSmooth`), the relative-root sign comparison
  (`relativeRootSignInclusions`, `relativeRootNegation`) gives
  `U(χ) ≤ P(ψ)`. Then `P(ψ)` is the exact extension of its inverse image along
  `j`, which is a dynamic parabolic of `L`.
- The inverse laws and the reflection of inclusion are the separated-group
  all-test identities `comap_extendFromCentralizer`,
  `extendFromCentralizer_comap` and `extendFromCentralizer_le_iff`; the
  separatedness instance comes from `hG.isSeparated`.

## Development check

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiled this
module with no errors or warnings. Inspection of
`Langlands.GroupScheme.dynamicLeviParabolicCorrespondence` reported only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance and scope

This module states no new mathematics; it is an internal assembly of
published Library results. The classical sources for the target are recorded
in its statement Markdown: Renard, *Représentations des groupes réductifs
p-adiques* (edition of 9 July 2026), V.3.11 (printed p.112/PDF p.118);
Borel–Tits, *Groupes réductifs* (1965), Proposition 4.4(c) (printed
pp.86–87); and Milne, *Algebraic Groups* (2017), §§25.1, 25.6–25.7. The Lean
route does not follow Borel–Tits 4.4(c): it uses rational conjugacy of maximal
split tori and the actual relative-root sign comparison instead. The proofs
and sources of the seven inputs are documented in their own paired Markdown.
