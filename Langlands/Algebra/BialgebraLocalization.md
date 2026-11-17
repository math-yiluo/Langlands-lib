# Spreading bialgebra isomorphisms from a localization

This internal specialization of `Langlands.BialgebraSpreading.exists_bialgEquiv`
uses the published description of a localization `M⁻¹R` as a directed limit
of principal localizations `R[1/s]`, for `s ∈ M`. It retains one arbitrary
universe `u`.

`Langlands.BialgebraSpreading.awayMapAlgHom M a b h` is the transition
`R[1/a] →ₐ[R] R[1/b]` when `a` divides `b`, for indices in the existing
`UnramifiedFunctor.Charts.DivIndex M`. It uses the actual localization map
`Charts.awayMap`, with its equation on original coefficients supplying the
algebra-map law. The identity and composition equations of those maps give
the `DirectedSystem` instance `awayDirectedSystem`.

For a commutative `R`-algebra `L` satisfying `IsLocalization M L`, the local
instances `awayAlgebra` and `awayTower` give its compatible algebra structures
over each principal localization. `isDirectLimit_away` proves the explicit
`IsDirectLimit` predicate. Its three fields are the published localization
witnesses: every fraction comes from some principal localization, equality of
two fractions holds at a common later principal localization, and the maps to
`L` commute with transitions. No injectivity of `R → L` is assumed.

`exists_away_bialgEquiv M L A B e` states that if `A` and `B` are commutative
bialgebras, finitely presented as `R`-algebras, and their scalar extensions to
`L` are bialgebra equivalent, there is an `s ∈ M` for which their scalar
extensions to `Localization.Away s` are bialgebra equivalent. It applies the
general directed-limit spreading theorem to the preceding explicit system,
then returns the underlying ring element of the chosen index. Hopf algebras
are included. Algebra finite presentation is the finiteness condition; module
finiteness, flatness, noetherian hypotheses and domain hypotheses are absent.

The provenance is internal: the module combines the actual localization
maps and fraction/equality witnesses from the published
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocalization` with
the proved bialgebra-spreading theorem. It does not assume a separate
localization-spreading assertion. In particular, taking `M` to be the
complement of a prime gives an actual principal neighborhood of that prime.
