# Evaluation through an exact derived functor

Author: Worker 13.

This internal categorical construction uses Mathlib's exact derived functor and
its canonical comparison with `DerivedCategory.singleFunctor`. Given a
single-degree comparison `s : K ≅ single_B(q)(X)`, the definition
`exactDerivedEvaluationSingleIso` first applies the actual exact derived
functor `E.mapDerivedCategory` to `s`, then applies its single-degree comparison
at `X`. Its target is `single_T(q)(E(X))`.

The abelian categories `B` and `T` have independent chosen derived localization
universes `wB` and `wT`. The functor `E : B ⥤ T` is additive and preserves
finite limits and finite colimits. No comparison of derived categories or
recovery theorem is supplied as part of `E`.

The theorem `exactDerivedEvaluation_single` starts with an already proved
equation `s.inv ≫ g ≫ t.hom = single_B(q).map h`. It proves that evaluation
of `g`, conjugated by the two constructed evaluated endpoint comparisons,
equals `single_T(q).map (E.map h)`. The proof combines preservation of
composition by the exact derived functor with naturality of Mathlib's
`mapDerivedCategorySingleFunctor q`. The input equation is retained explicitly;
the theorem constructs no recovery result without it.

This helper supports evaluation of whole local coefficient diagrams after
changing source. It is an internal consequence of Mathlib's
`Algebra.Homology.DerivedCategory.ExactFunctor`, with no new direct literature
assertion. All equations are proved in Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, without new axioms or proof holes.
