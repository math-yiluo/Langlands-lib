# Reduction of the dynamic case of C.1.6 to separably closed fields

Authors: Worker 254, Worker 266.

This module reduces the dynamic pseudo-reductive case of CGP Proposition
C.1.6 to separably closed base fields. That case is the proposition
`DynamicParabolicQuotientDVRLifting k` of
`Langlands.GroupScheme.PseudoParabolicQuotientDynamicCase`. For a field `k`,
it says the following. Let `G` be a pseudo-reductive group over `k`,
`χ : 𝔾_m ⟶ G` a cocharacter, and `q : G.X ⟶ Q` a smooth, surjective,
quasi-compact morphism of `k`-schemes whose fibres on all test schemes are
the right cosets of `P_G(χ)` (`Dynamic.parabolic χ`). Then `Q` has the DVR
lifting property `PseudoComplete.HasDVRLifting`. Everything lives in the
namespace `Langlands.GroupScheme`.

## Main results

- `dynamicParabolicQuotient_baseChange`: for any morphism of base schemes
  `b : S' ⟶ S`, a group scheme `G` over `S`, a cocharacter `χ` and a morphism
  `q : G.X ⟶ Q` over `S`, base change along `b` preserves all the hypotheses
  on `q` in
  `DynamicParabolicQuotientDVRLifting`. Concretely, if `q.left` is smooth,
  surjective and quasi-compact and `q` satisfies the fibre criterion, then
  `((Over.pullback b).map q).left` is smooth, surjective and quasi-compact,
  and the base-changed `q` satisfies the fibre criterion for
  `Dynamic.parabolic (Dynamic.baseChangeCocharacter b χ)` on all test schemes
  over `S'`.
- `dynamicParabolicQuotientDVRLifting_of_isSepClosed`: assume `hsep`, the
  Library statement `PseudoReductiveSeparableExtensionStatement.{u}` (module
  `Langlands.GroupScheme.Reductive.PseudoReductiveSeparableExtensionStatement`).
  It says that for every separable algebraic extension `K/k` of fields in
  `Type u` and every pseudo-reductive `G` over `k`, the base change of `G` to
  `K` is pseudo-reductive. Assume `hsc`, that
  `DynamicParabolicQuotientDVRLifting k` holds for every separably closed
  field `k : Type u`. Then `DynamicParabolicQuotientDVRLifting k` holds for
  every field `k : Type u`.

`PseudoReductiveSeparableExtensionStatement` is the separable case of CGP
Proposition 1.1.9(1). This module proves neither `hsep` nor `hsc`; both are
hypotheses of the theorem.

## Proof

`dynamicParabolicQuotient_baseChange`. Smoothness, surjectivity and
quasi-compactness are stable under base change
(`MorphismProperty.overPullbackMap`). The fibre criterion is
`dynamicParabolicQuotient_fiber_baseChange` from
`Langlands.GroupScheme.Dynamic.QuotientFiberBaseChange`.

`dynamicParabolicQuotientDVRLifting_of_isSepClosed`. Let
`L = SeparableClosure k` and `b = Spec L ⟶ Spec k`. `L` is separably closed
(`SeparableClosure.isSepClosed`), and `L/k` is separable and algebraic. The
base change `G_L` is pseudo-reductive by `hsep` applied to `k`, `L` and `G`. Then
`dynamicParabolicQuotient_baseChange` provides the hypotheses for
`G_L`, `χ_L = Dynamic.baseChangeCocharacter b χ` and the base-changed `q`.
So `hsc L` gives the DVR lifting property for `Q_L = (Over.pullback b).obj Q`
over `L`. It descends to `Q` by `PseudoComplete.hasDVRLifting_of_baseChange`
(in `Langlands.GroupScheme.PseudoCompleteAlgebraicBaseChange`), since `L/k` is
algebraic.

## Provenance

This reduction formalizes a step in the proof of Proposition C.1.6 in Conrad,
Gabber and Prasad, *Pseudo-reductive groups* (2nd ed.), printed p.586. After
reducing to pseudo-reductive `G`, the proof says: "To prove the
pseudo-completeness of G/P it is harmless to make a separable extension on k,
so we can assume that k = k_s." The justification is left implicit there. It
consists of the preservation of pseudo-reductivity under separable extension
of the ground field (Proposition 1.1.9(1)) and the descent of
pseudo-completeness (Proposition C.1.2(2)). The formalization replaces
pseudo-completeness by its DVR lifting half. Separatedness and
finite type are hypotheses of the target statement. The descent used is the
algebraic-extension descent of the DVR lifting property proved in
`PseudoCompleteAlgebraicBaseChange`. The base-change compatibility of the
fibre criterion is the internal lemma of
`Langlands.GroupScheme.Dynamic.QuotientFiberBaseChange`.
