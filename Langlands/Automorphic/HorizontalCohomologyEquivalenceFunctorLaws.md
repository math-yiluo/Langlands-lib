# Inversion and functor laws for actual horizontal equivalences

For an arbitrary-universe number field `F : Type u`, positive natural rank
`n` (`NeZero n`), and actual complex operator realizations `S`, `T`, `U`,
this internal API describes the existing finite adelic equivalences on
actual horizontal cycles and their image-boundary quotient in every natural
degree `q`, including zero.

`horizontalCyclesEquiv_symm` and `horizontalCohomologyEquiv_symm` identify
the inverse of the induced cycle or quotient equivalence with transport
by the inverse full operator equivalence `e.symm`.
`horizontalCyclesEquiv_refl` and `horizontalCohomologyEquiv_refl` identify
transport of the identity full operator equivalence with the identity
equivalence of the existing finite adelic cycle or quotient representation.
`horizontalCyclesEquiv_trans` and `horizontalCohomologyEquiv_trans` identify
transport of `e.trans g` with transport by `e` followed by transport by `g`.
All equalities concern bundled representation equivalences, so finite
adelic equivariance is retained together with the underlying maps.

The six declarations are typed proof abbreviations. Each proof first uses
representation-equivalence extensionality. For cycle equivalences, two
subtype extensionality steps remove membership proofs, alternating-map
extensionality evaluates on a reduced Lie-algebra tuple, and the coefficient
equation is reflexive. For quotient equivalences, direct quotient induction
chooses a cycle representative; the defining forward or inverse quotient
computation reduces the goal to equality of projected cycles. Congruence
under the actual class projection then gives the same coefficient proof.
No surjectivity alias or simplifier attribute is used.

Twelve explicitly named local additive groups are exactly the canonical
submodule structures on the five function-space stages, three realization
spaces, three exact generic horizontal cochain spaces, and the generic
cycle-space family parametrized by realization and degree. They do not
alter carriers or operations and add no hypotheses.

The provenance is internal specialization and direct computation of
`HorizontalCohomologyEquivalence`, `HorizontalCohomologyClasses`, and the
published generic cycle and quotient equivalence constructors. Actual
full-standard-compact cochain conditions, differential kernels and actual
image-boundary quotients are retained. The unit makes no external-literature
comparison, analytic comparison, topology, smoothness, nonvanishing,
irreducibility, spectral-existence or broad infrastructure completion claim.
