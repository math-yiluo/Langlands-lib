# Evaluation of the original algebraic-space Weil counit

This internal construction extends the published scheme counit evaluation to
actual algebraic-space ring points. It uses the same original test spectra and
coefficient maps. No representability theorem or topology comparison is claimed.

Let `B` be an `A`-algebra, let `R` be an `A`-algebra, and let `D` be a
`B`-algebra. A ring homomorphism `f : R → D` is compatible when its composite
with the `A`-action equals the composite of the `B`-action with `A → B`.
For an algebraic space `X` over `B`, assume that the actual Weil restriction
sheaf is algebraic. Its sections on `Spec R` are sections of `X` on the
actual base-changed test spectrum. `spaceWeilRestrictionEvaluation` pulls
these sections back along `weilRestrictionEvaluationTest` for `f`.

The lower and upper naturality theorems assert that this evaluation commutes
with compatible coefficient changes in `R` and in `D`, respectively. The proofs
compose presheaf pullbacks and use the published equalities of the same test
maps. No injectivity or geometric condition on these coefficient maps is needed.

`completedTensorSpaceWeilRestrictionPointMap_eq_evaluation` identifies an
original local tensor component, after an original lower coefficient projection,
with evaluation on the whole coefficient ring. Its hypotheses give a tensor
product decomposition and its original upper coefficient law. The specified
component coefficient equals the original lower projection followed by the
local coefficient map. The proof again composes presheaf pullbacks and applies
the existing equality of completed-tensor and evaluation test maps.

Finally, `ringWeilRestrictionPointsEquiv_eq_evaluation` identifies the usual
Weil point equivalence followed by a specified `B`-algebra map from `B ⊗[A] R`
with this evaluation, provided its value on `1 ⊗ r` is `f r`. This algebra map
need not be an equivalence. The proof compares the two actual test maps by
both projections of the pullback and then composes presheaf pullbacks.

The provenance is internal reuse of `PointTopology.WeilRestrictionEvaluation`
and the actual space tensor-point definitions. These identities provide the
coefficient compatibility needed to identify arithmetic stage comparisons with
the original full adelic counit; they do not prove that global comparison.
