# Local bijectivity on analytic quasi-étale sites

These internal definitions construct witnesses that module sheafification inverts exactly
the locally injective and locally surjective morphisms on the ordinary and
twisted analytic quasi-étale sites.

Let `K : Type u` be a complete ultrametric normed field,
`X : LocalizedCategory.{u,v,v} (K := K)`, and
`R : Type (max u (v + 1) uL)` a commutative ring. The coefficient universe `uL`
is arbitrary. `quasiEtale_wEqualsLocallyBijective X R` supplies the Mathlib
property `WEqualsLocallyBijective` for `quasiEtaleTopology X` and module
coefficients. Here `W` is the class of presheaf morphisms inverted by
sheafification.

For `ρ : G →* Aut X` with `G : Type z` a group small in the coefficient
universe, `twistedQuasiEtale_wEqualsLocallyBijective X R ρ` supplies the same
property for `twistedQuasiEtaleTopology ρ`. These results require neither
compactness nor a continuous action.

The named witnesses are reducible definitions (`abbrev`), available for
explicit downstream use without global instance registration. Each is
defined by a complete proof using the established essential smallness and local smallness of the
two analytic sites. Module categories have the required limits over the
structured-arrow categories of their small models. Mathlib's
`GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` then
transports the concrete-category characterization on each small model back
to the actual site.

The provenance is internal: these are specializations of the existing
small-site transport theorem using the analytic size results from
`AnalyticQuasiEtaleCompactCohomology`. In particular, the ordinary result
discharges the technical local-bijectivity assumption retained in
`CompactCechSystem` and `CompactCechAcyclic`. The finite nerve presentation
and restricted-injective Hom exactness obligations for the global comparison
remain open.
