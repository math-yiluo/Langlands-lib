# The ample coherent Euler coefficient criterion

`AmpleCoherentEulerCoefficientInDimension d` asserts the following criterion
for every actual coherent module `M` on a Noetherian separated scheme proper
over a field, in arbitrary universe `u`. If `L` is ample and
`HasSupportDimensionLT M (d + 1)` holds, coefficient `d` of
`coherentEulerPolynomial f M hM L d` is nonnegative, and it is positive
exactly when `HasSupportDimensionLT M d` fails. Quasi-coherence and finite
affine sections are the explicit coherence hypotheses. The polynomial is the
Newton reconstruction of actual derived-cohomology Euler characteristics.

`AmpleCoherentEulerCoefficientReductionStatement` states a reduction to the
existing `CoherentIntegralIdealFiltrationStatement`: if that finite-filtration
theorem holds for Noetherian schemes, the coefficient criterion holds for all
natural `d`. The filtration premise retains its entire original content:
actual closed-immersion pushforwards of nonzero coherent ideals on integral
schemes, connected by actual short exact sequences. It is not a positivity
premise.

The intended internal derivation is induction on `d`. Finite-support Euler
positivity supplies the dimension-zero case. On an integral scheme of
dimension `d + 1`, a coherent ample-section cokernel of dimension exactly `d`
has positive coefficient by induction. Its actual short exact section sequence
identifies that coefficient with a positive scalar times the structure-module
coefficient at `d + 1`. Nonzero ideals have the same top coefficient as the
structure module, since their quotient has smaller support. Closed pushforward
preserves Euler polynomials and support bounds, and finite coherent filtration
additivity transfers the criterion from integral ideal factors to every `M`.

This statement is an internal reduction, not a proof of the filtration premise
or of the host smooth proper line-bundle theorem. The host result requires an
actual proof of the filtration theorem before applying this reduction.
