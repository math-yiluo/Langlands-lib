# Affine analytification and étale morphisms

The theorem `Langlands.Analytic.AffineAnalytification.affineAnalytificationEtale`
proves `AffineAnalytificationEtaleStatement.{u, v, w}`. The argument uses the
Library theorems `affineAnalytificationQuasiFinite`,
`affineAnalytificationFiniteGermComparison`, and
`SchemeAnalytification.analytificationCenter`.

The affine center map is surjective by `SchemeAnalytification.analytificationCenter`.
Choose an analytic point over a prescribed prime of \(B\), and choose an
original chart containing it. The definition of the center identifies that
prime with the contraction of the chart point's seminorm kernel along the
polynomial-locus algebra map.

For the unramified comparison, the polynomial presentation makes \(B\) of
finite type over \(K\), hence over \(A\). Mathlib then gives quasi-finiteness
of a formally unramified map. The quasi-finiteness comparison gives
finiteness at every analytic point. A chart containing such a point permits
application of the finite-germ comparison there, and
`Algebra.formallyUnramified_iff_forall` supplies formal unramifiedness at its
center. Conversely, analytic unramifiedness includes finiteness at the
point. Lift each algebraic prime to a chart point and apply the finite-germ
comparison to obtain formal unramifiedness at that prime. The same Mathlib
criterion yields global formal unramifiedness.

For flatness, algebraic quasi-finiteness again supplies finiteness at each
analytic point. Flatness of the algebraic map localizes to the local map at
each chart point's center. The finite-germ comparison gives analytic flatness
at each point. Conversely, analytic flatness implies analytic quasi-finiteness,
so the quasi-finiteness comparison detects algebraic quasi-finiteness. Lift
each algebraic prime to a chart point and use the finite-germ comparison to
obtain flatness of the local ring map. The proof of global flatness applies
`Module.flat_of_isLocalized_maximal` to \(B\) as an \(A\)-module. At each
maximal ideal of \(B\), it composes the flat local ring map with the flat
localization of \(A\) at the contracted ideal. This works with \(A\) and \(B\)
in independent universes.

For étaleness, `RingHom.Etale.iff_flat_and_formallyUnramified` also requires
finite presentation. It follows from relative finite type and Noetherianity
of \(A\), which is of finite type over \(K\). Formal unramifiedness again
supplies quasi-finiteness. Étaleness therefore combines the two algebraic
properties already compared, matching the conjunction in the definition
of analytic étaleness. The proof includes zero algebras.

The global comparison is the affine case over \(K\) of Berkovich's
Propositions 3.2.10 and 3.3.11 in *Étale cohomology for non-Archimedean
analytic spaces* (1993), printed pp. 60 and 64. In the Lean argument the
finite-germ comparison supplies the analytic local algebra step. The
statement companion records the precise match with the Library predicates.
[AffineAnalytificationEtaleStatement.md](AffineAnalytificationEtaleStatement.md)
