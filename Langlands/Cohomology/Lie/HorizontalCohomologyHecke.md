# Smooth chain actions and Hecke integration on horizontal cohomology

This internal construction starts with the existing complex Lie algebra `L`,
its actual Lie module `M`, a submodule `H`, and the group representations
`σ` and `ρ` with their bracket and infinitesimal compatibility laws. These
are the inputs to the existing full-group horizontal differential, its
kernel cycles and its quotient by differential-image boundaries. The Lie
algebra, module, compact-acting group `G` and translating group `P` have
independent universes.

The translating group is a group with a topology. Its given action in every
cochain degree must commute with the actual differential. The construction
`cyclesActionInclusion` bundles the existing cycle subtype inclusion as an
intertwiner. `differentialActionIntertwiner` bundles the original differential
using precisely that chain compatibility. If each cochain action is smooth,
in the existing open-subgroup sense, cycle smoothness follows by injective
transfer. Cohomology smoothness follows by surjective transfer through the
existing quotient projection. Neither conclusion assumes finite-dimensional
cohomology or a topology on the coefficient module.

If `P` is a topological group with a Borel measurable structure and Haar
measure `μ`, `cochainHeckeAction`, `cyclesHeckeAction` and
`cohomologyHeckeAction` integrate these same actions using the existing
`Hecke.heckeAction`. They are nonunital complex algebra homomorphisms from
the actual measure-indexed Hecke algebra to the endomorphisms of the original
spaces. The differential, cycle inclusion and cohomology projection commute
with integration, by applying `Hecke.integratedAction_intertwiner` to the
three original intertwiners. Consequently the quotient operator agrees with
the integrated operator on every cycle representative. All degrees are
natural numbers, including degree zero where the original boundaries vanish.

The provenance is internal: the existing horizontal cohomology construction,
smoothness transfer, and measure-indexed integration already supply the
mathematical operations and laws. No external-source identification or
normalization is added. Smoothness of the original cochain actions and chain
compatibility are explicit premises. This construction establishes no
existence, admissibility, nonvanishing, spectral occurrence or arithmetic
comparison of an automorphic realization.
