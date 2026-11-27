# Compact charts for a realized common-Levi pair

`realizedTwistCoefficientEquiv` extends the inducing equivalence at every
parameter when the two characters agree on the actual Levi inclusion.
Its linear map is the original equivalence. The Levi-inflated induction
of this map acts pointwise and `realizedLowerCompactEquiv` follows that
map by the actual `compactEquiv`.

The common-Levi charts have the prescribed evaluations in
`compactEquiv_eval` and `realizedLowerCompactEquiv_eval`. Applying
`exists_realizedFixedCompactRestriction` gives one fixed surjective
restriction compatible with the actual stages map throughout the
unramified parameter space.
