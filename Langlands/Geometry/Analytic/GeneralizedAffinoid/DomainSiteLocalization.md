# Localization of the finite full-domain site

This internal construction lifts the published full-domain category equivalence
`d.localizationEquivalence` to the finite point-covering Grothendieck topologies.
Here `K` is a complete ultrametric normed field, `A` is an actual presented
positive-polyradius affinoid algebra, and `d` is a full represented domain over
`A`. The source site has objects `Domain K d.algebra`; the target is the slice
`Over d` with the topology induced from `finiteDomainTopology K A`.

Both actual functors are cocontinuous. For extension, a finite covering family
in a slice sieve is restricted to the actual algebra of `d`. The inverse-image
locus formula proves coverage. The equivalence's counit and downward closure of
the original sieve prove membership of the extended arrows. For restriction,
extend each component of a finite covering family and compose its image arrow
with the counit. The original locus-image formula proves ambient coverage;
the unit and downward closure prove membership after restriction. Uniqueness of
actual bounded domain restrictions identifies the required composite arrows.

Mathlib's equivalence-of-sites results then supply dense-subsite instances in
both directions and `localizationSheafEquivalence` for an arbitrary coefficient
category, with independent object and morphism universes. Its forward functor
precomposes the underlying presheaf with `d.relativeFunctor.op`; its inverse
precomposes with `d.extendOverFunctor.op`, as the two displayed formulas state.
No coefficient limits, sheafification, or assumed descent result are required.

The provenance is an internal deduction from `DomainLocalization`,
`DomainCovering`, and Mathlib's slice topology and sheaf equivalence. There is no
new original-literature assertion. Arbitrary positive radii, trivial valuations,
nilpotents, zero algebras, empty spectra, and permitted empty finite covers are
retained. This is localization of the finite site over a fixed affinoid; the
unrestricted analytic G-topology, general analytic atlases, etale and equivariant
sites, and the Harris tower remain separate obligations.
