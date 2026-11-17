# Wave packets preserve the fixed input level

This internal construction supplies the fixed-subgroup invariance needed for
Schwartz synthesis from level estimates. It uses the Library's actual coherent
orbit sections, compact-probability coefficients, and wave-packet integral.

For an arbitrary open subgroup `H`, a section of `OrbitSectionLevel H` is fixed
by the product action of `H × H`. The theorem
`unitaryOrbitCoefficientMap_biInvariant_of_level` proves that every one of its
coefficient functions is bi-invariant under that same `H`, simultaneously at
every discrete-series orbit class. There is no shrinking of `H` depending on
the section or orbit class. In particular this applies uniformly to each
fixed input level with `H` contained in the compact packet subgroup.

The proof chooses an inducing representative of the orbit class, applies the
published representative formula, and evaluates the section's product-action
invariance at this representative. The product element `(l, k⁻¹)` acts on the
coefficient by the translation `g ↦ k * g * l`, by the published compact
coefficient action law. These two equalities give the asserted invariance.

The theorem `inducedOrbitWavePacket_biInvariant_of_level` integrates that
pointwise equality with the original weight and orbit measure.
`inducedOrbitWavePacketLevel` packages the same integral as a function taking
values in the subtype of functions bi-invariant under `H`; its application
formula is definitional. Neither this invariance equality nor its integration
requires a seminorm bound, a bounded weight, or an integrability hypothesis.
No linearity or decay is inferred from integration here.

The construction is derived from `OrbitSectionTopology`, the representative
and action formulas in `ProductInducedOrbitCoefficients`, and the integral in
`OrbitWavePacket`. The integral is the one defined in Waldspurger's VI.3,
printed p.302 (PDF p.68) of the registered 2003 Plancherel paper, with a general
weight and character measure. The implemented fixed-level argument is internal.
It proves neither the actual derivative estimates nor the full membership and
continuity assertions of VI.3.1.
