# Underlying transport and class formulas for actual horizontal equivalences

For a number field `F : Type u`, positive rank `n : ℕ` (`NeZero n`), actual
complex operator realizations `S`, `T` and a full operator equivalence
`e : S.Equivalence T`, this internal API describes the existing
`e.horizontalCyclesEquiv q` and `e.horizontalCohomologyEquiv q` in every
natural degree, including zero.

`horizontalCyclesEquiv_toIntertwiningMap` and
`horizontalCohomologyEquiv_toIntertwiningMap` identify their forward bundled
finite adelic intertwiners with the existing actual
`Intertwiner.horizontalCyclesMap e.toIntertwiningMap q` and
`Intertwiner.horizontalCohomologyMap e.toIntertwiningMap q`, respectively.
The underlying maps and finite equivariance are precisely the published
transport, without a replacement cohomology carrier.

`horizontalCyclesEquiv_val` identifies the underlying transported cochain
with `e.horizontalEquiv q f.val`. `horizontalCyclesEquiv_apply` evaluates a
transported cycle at a reduced Lie-algebra tuple `X`: its value is
`e (f.val.val X)`. The forward representative law
`horizontalCohomologyEquiv_class` sends the source class of an actual cycle
to the target class of its transported cycle. The inverse representative law
`horizontalCohomologyEquiv_symm_class` uses the inverse cycle equivalence
to describe the inverse quotient equivalence on every target cycle class.

All six declarations are typed proof abbreviations with reflexive proofs.
The generic equivalence construction uses the same restriction and quotient
maps as the generic intertwiner construction. Actual horizontal cochain
equivalences and maps have the same forward coefficient postcomposition,
and their chain-compatibility proofs are propositionally irrelevant.
The representative laws are the defining quotient computations, in the
forward and inverse directions. No simplifier attribute is installed.
Ten explicitly named local additive groups are exactly the canonical
submodule structures on the five function-space stages, the source and
target realization spaces, their exact generic cochain spaces, and generic
cycles parametrized by realization and degree.

The provenance is internal computation of
`HorizontalCohomologyEquivalence`, `HorizontalCohomologyTransport` and
`HorizontalCohomologyClasses`, with the corresponding published generic
cycle/quotient constructors. Actual differential kernels and actual
image-boundary quotients, full standard infinite compact equivariance and
finite adelic actions are retained. There is no external-literature
comparison, identity/composition law, topology, smoothness, nonvanishing,
irreducibility or broad infrastructure completion claim in this pair.
