# An even power preserving the actual carried Harris lattice

This internal unit concerns the original Harris compact level, actual positive
polarized action object, compatible full Tate frames and rational self-isogeny.
It uses the existing `Prerequisites` package for the carried lattice construction.

`EvenIntegralPowerWitness` asserts the existence of an actual compatible frame
and a positive integer m such that q^(2m)=1 and the actual full rational Tate
operator of the underlying rational self-isogeny to the power 2m preserves the
frame's integral finite-adele lattice in both directions. The lattice is the
existing `harrisIntegralFrameLattice`, the literal image of the fixed Harris
integral source span under that frame.

`evenIntegralPowerWitness_of_levelIso_fixed` proves this assertion for every
self-isogeny fixing an orbit at any original Harris compact level. The proof
chooses the actual frame and original subgroup element supplied by fixedness.
Its corresponding scalar-extension similitude lies in the transported compact
level. Intersecting that level with the open source-lattice stabilizer has
finite index: its coset space is compact and discrete. The finite-index power
lemma supplies a positive power of the square of this element that lies in the
source-lattice stabilizer.

The proved compact-multiplier comparison gives |q|=1, hence q^2=1 and
q^(2m)=1. Induction on powers of the actual frame equation identifies the full
rational Tate operator with the corresponding source operator in frame
coordinates. Source-lattice stabilization therefore gives exactly the stated
two-way preservation of the actual carried lattice. Existing integer-bound
results for that same carried lattice remain available to consumers.

This result assumes no finite order of the self-isogeny and uses no multiplier
positivity theorem. It proves lattice preservation by a positive even power,
not that the rational self-isogeny has finite order. Realization of the lattice,
transport of the polarization, finiteness of integral polarized automorphisms
and the final small-level rigidity conclusion remain separate obligations.
The provenance is the imported actual frame, compact-multiplier, carried
lattice and open-stabilizer constructions together with Mathlib's finite-index
power lemma; no additional external literature assertion is made.
