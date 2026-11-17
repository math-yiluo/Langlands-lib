# Renard VI.10.6 Proposition (i) from its named inputs

Author: Worker 733, Task 6639 (`97df9594-40e0-45d8-8f8c-0e7562c6b4de`).

This module proves two conditional theorems. They reduce the published
`Langlands.Jacquet.StandardIwahoriFixedVectorBlockDecompositionStatement`
(Renard VI.10.6 Proposition (i), `M(G)_K ≃ ∏_{𝔰 ∈ B(G)_K} M(G)_𝔰`), and the
fixed-vector visibility of Bernstein classes, to three published Library
statements. Their proofs are separate obligations. The module proves neither
the target nor visibility unconditionally.

## Statements

The three hypotheses are exactly these published Library statements:

- `hBernstein`: `CuspidalSupport.BernsteinDecompositionStatement.{uF, uV}`
  (Renard VI.7.2, the Bernstein decomposition of the category);
- `hCrit`: `CuspidalSupport.StandardRepresentativeFixedVectorCriterionStatement.{uF, uV}`
  (Renard VI.10.6, first claim of the proof of the Corollary: `[a]_G ∈ B(G)_K`
  iff the cuspidal representation of the datum `a` has a nonzero
  `K ∩ M_a`-fixed vector);
- `hAssociate`:
  `Aubert.General.RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV}`
  (Renard VI.5.4, Theorem, for represented parabolics).

The module proves the following.

- `standardIwahoriBernsteinFixedVectorVisibility_of_inputs hCrit hAssociate`
  takes the binders, hypotheses and `letI` instances of the target statement,
  in the target's order, up to and including `_hIwahori` and the three
  instances `T2Space F`, `LocallyCompactSpace (rationalPoints G)` and
  `NonarchimedeanGroup (rationalPoints G)`. It concludes
  `bernsteinFixedVectorVisibility.{uF, uV} i ν (standardBernsteinFamily i ν hG hi hν) K`.
  This is the conditional form of the visibility helper required by the task.
- `standardIwahoriFixedVectorBlockDecomposition_of_inputs hBernstein hCrit hAssociate`
  has type exactly `StandardIwahoriFixedVectorBlockDecompositionStatement.{uF, uV}`.
- `standardIwahoriFixedVectorBlockDecompositionOfInputs` is the same
  implication stated as a declaration whose type is the implication: the
  three hypotheses in the order above, then the target. It is a `def` of
  Prop-valued type, so the `defProp` linter is disabled for this declaration
  only.

The field universe `uF` and the carrier universe `uV` stay independent. The
association statement is used at carrier universe `max uF uV`, where the
inertial supports of the target live. The proofs add no premise beyond the
three hypotheses. They add no admissibility, finite-length or
canonical-section premise. In particular, they use neither the Library's
admissibility statement nor the canonical-section statement for `K`.

## Proof

For the visibility theorem, the proof introduces the binders and instances
of the target. It applies `bernsteinFixedVectorVisibility_of_uniqueness_of_necessity`
(module `StandardIwahoriVisibilityReduction`) to the standard family, with
three inputs:

- `_hstandard`, compactness of `K` and `_hIwahori` from the binders;
- support uniqueness
  `bernsteinInertialSupportUniqueness_of_represented i ν family hAssociate`,
  a published reduction of uniqueness to VI.5.4;
- the forward direction of `hCrit`, applied to the same binders.

The binders `K₀`, `_hK₀`, `_hIwasawa`, `_hKK₀` and `_hnormal` are used only
to instantiate `hCrit`.

For the block decomposition, the proof introduces the same binders and an
object `V`. The direction (⇒) is
`isCoproductOfFixedClasses_of_fixedVectorGenerated` (module
`StandardIwahoriBlockDecompositionReduction`), applied to the first component
of `hBernstein` at the standard family. That component says every object is
a coproduct of block objects. The direction (⇐) is
`fixedVectorGenerated_of_isCoproductOfFixedClasses` (same module), applied to
the visibility just proved. The index predicate `bernsteinFixedClass` of that
module unfolds to the target's index predicate, so the conclusion has the
target's exact form.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VI.10.6: the Theorem and its proof, the
Proposition (i) and its proof, and the proof of the Corollary (printed
pp.213–215 / PDF pp.219–221). The inputs are VI.7.2 (printed pp.181–184 / PDF
pp.187–190) and VI.5.4 (printed pp.173–175 / PDF pp.179–181). Registered
source `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The provenance is derived. Renard deduces Proposition (i) from the Bernstein
decomposition together with the fact that `K`-fixed vectors are visible on
inertial classes. The latter comes from the criterion of the Corollary's
proof and Jacquet's lemma. The implemented route uses the admissibility-free
nonvanishing form of Jacquet's lemma (module `IwahoriJacquetNonvanishing`)
and only the necessity direction of the criterion. Once proofs of the three
input statements are published, applying these theorems to them proves the
target and the visibility helper unconditionally. Those statements are the
targets of Task 5313 (VI.7.2), Task 6561 (the criterion), and Task 4949 or
Task 6571 (VI.5.4 / support uniqueness).
