# Actual horizontal quotient transport and projection

For a number field `F : Type u` in an arbitrary universe, positive natural
rank `n`, actual operator realizations `S` and `T`, and a full operator
intertwiner `A : S.Intertwiner T`, this module gives two computation laws for
the previously constructed `A.horizontalCohomologyMap`. The coefficients are
complex. Every natural cochain degree is included, including degree zero.

The carriers are unchanged: `S.horizontalCycles q` is the kernel of the actual
horizontal differential, and `S.HorizontalCohomology q` is its quotient by the
actual boundaries inside cycles. The horizontal cochains retain every-slot
horizontality and equivariance under the entire standard infinite compact
group. The finite adelic representations and quotient projections are those
already constructed in `HorizontalCohomologyFinite`.

`Intertwiner.horizontalCohomologyMap_class` states that the class of an actual
cycle `f` is sent to the class of `A.horizontalCyclesMap q f`.
`Intertwiner.horizontalCohomologyMap_class_comp` states the same naturality as
equality of bundled finite adelic intertwiners: quotient transport composed
with the source projection equals the target projection composed with cycle
transport. No chain equation or desired transport property is added as an
input; the construction core already proves the required compatibility.

The first proof is reflexivity of the existing quotient construction. For the
second, intertwiner extensionality and linear-map extensionality reduce the
bundled equality to its value on a cycle; this is again reflexivity. Both
results are typed proof abbreviations, without simplifier attributes.

This is internal API content derived directly from
`HorizontalCohomologyTransport`, `HorizontalCohomologyClasses`, and the generic
`Langlands.Cohomology.Lie.HorizontalCohomologyIntertwiner` constructions. It
makes no new identification with external literature. Ten named local
additive-group instances use only canonical `Submodule.addCommGroup`
structures: five on the successive function spaces, two on the realization
spaces, two on their generic horizontal cochain submodules, and one
parametrized by any operator realization on its generic cycle submodule.
These instances do not change the mathematical carriers or operations.

Quotient identity and composition, underlying-linear-map formulas, and
operator-equivalence specializations are separate obligations. This module
asserts no smoothness, topology, finiteness, nonvanishing, analytic comparison,
or completion of the global infrastructure.
