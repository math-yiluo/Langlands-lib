# Normalized periods over `F^ι \ 𝔸^ι` are torus integrals

Module `Langlands.Global.RankinSelberg.DualExpansionLattice`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal.

- `ColGroup F ι = Multiplicative (ι → 𝔸)` with its Borel, second-countable and locally compact
  structures, and the discrete subgroup `ratLattice F ι` of rational vectors
  (`isDiscrete_ratLattice`). The quotient is compact (`compactSpace_ratLattice_quotient`) when
  `𝔸 / F` is.
- `colReduce` is the reduction `ColGroup F ι → (𝔸 / F)^ι`. `map_colReduce_restrict`: the image
  of Haar measure restricted to the chosen fundamental domain of `ratLattice` is the mass of the
  fundamental domain times the torus Haar probability.
- `normalizedPeriod_ratLattice`: for a continuous `ratLattice`-invariant `f`, the normalized
  integral of `f` over the chosen fundamental domain equals the torus integral of
  `y ↦ f(ofAdd y)`. This identifies the Library's abstract normalized periods with torus
  integrals.
