# Exact transitivity of actual model coefficient extension

This internal construction compares two successive coefficient extensions of
an actual integral model with direct extension. All coefficients have
arbitrary common universe `u`. Domains R, A and B have specified fraction
fields K, L and P. The coefficient algebras and scalar towers make the two
individual coefficient squares, the integral and field composites, and the
direct coefficient square commute. These are the explicit algebra and
scalar-tower hypotheses in the file.

`squareComparison_pasting` proves the general geometric identity: the
integral pullback tower followed by the comparison for the composite
coefficient square equals the two successive square comparisons followed by
the generic field tower. Its maps are the actual group-scheme pullback
comparisons. The proof projects all the way to the original group and uses
pullback extensionality and the established projection formulas.

`coefficientSpec_comp` expresses a scalar tower as an equality of the
contravariant spectrum maps. `coefficientTowerGenericIso` names the actual
comparison from the two successive field pullbacks to the direct one.
`baseChangeTowerIso` is an actual compatible integral-model isomorphism from
`(M.baseChange A L).baseChange B P` to `M.baseChange B P`, with precisely that
generic comparison. Its integral isomorphism is the actual integral
pullback-tower comparison. Its generic compatibility uses the proved
pasting identity, naturality in M's chosen generic identification, and the
public equality with the original coefficient generic comparison.

This is an internal consequence of actual pullbacks and existing coefficient
base change. It has no smoothness, arithmetic, point-stability or fpqc
premise, and proves no existence of coefficient models or final unramified
model descent.
