# Actual stages restriction through the represented Levi

`realizedLeviEquiv` is the inducing-group comparison from
`RealizedLeviTransport.centralizerEquiv` followed by the literal subgroup
equivalence. `realizedStagesRestriction` evaluates
`RealizedLeviStages.inductionInStagesIso` at the specified outer argument,
using `normalizedInductionLeviEquiv` for the source and target section
models. The linear coefficient identification is the identity on the
inducing carrier.

`realizedStagesRestriction_formula` gives the exact half-character
factor at each lower point. `realizedStagesRestriction_surjective`
transports `normalizedInduction_eval_surjective` through these maps.

`exists_realizedStagesRestriction_aligned` uses the same construction
with common-Levi decompositions based on equal literal subgroups. The
inducing-group equivalence is determined by its underlying point inclusion.
