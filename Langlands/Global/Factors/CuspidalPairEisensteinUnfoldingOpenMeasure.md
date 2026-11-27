# Normalized Haar measures on the open cell

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpenMeasure` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) normalizes the Haar measures of the three
groups of
[CuspidalPairEisensteinUnfoldingOpenGroups.md](CuspidalPairEisensteinUnfoldingOpenGroups.md)
by their rational lattices. It then identifies the normalized Haar measure of `N₀(𝔸)` with
the product of the normalized measures of the radical and of the block diagonal group, in the
coordinates `(Y, m) ↦ u'(Y) diag(m)`.

## Instances and finite covolume

- The radical `Radical F r t`, the matrix space `M_((t+1) × (r+1))(𝔸)` written
  multiplicatively, is locally compact and second countable, with its Borel σ-algebra
  (`radicalLocallyCompact`, `radicalSecondCountable`, `radicalMeasurableSpace`,
  `radicalBorelSpace`).
- `exists_isCompact_cover_Γ₀`: a compact subset of `N₀(𝔸)` meets every `N₀(F)`-orbit. This is
  `exists_isCompact_pattern_cover` with `J = ∅`.
- `isDiscrete_radicalLattice`: the preimage of `N₀(F)` in the radical is discrete.
  `isFiniteMeasure_radicalQuotient`: its quotient has finite Haar volume. With the compact
  `D ⊆ 𝔸` meeting every coset of `F`
  (`AdelicGroupPoints.exists_isCompact_algebraMap_add_mem`), every `Y` is moved into
  `D^((t+1) × (r+1))` by a rational matrix, and `u'(C)` is rational for rational `C`.
- `isFiniteMeasure_leviQuotient`: `N_(t+1)(F) × N_(r+1)(F) \ N_(t+1)(𝔸) × N_(r+1)(𝔸)` has finite
  volume, from the compact covers of the two factors.

## The normalized measures

- `haarH`, `haarN`, `haarM`: the Library's
  `LeftCosetSpace.Semidirect.latticeNormalizedHaar` for `N₀(F) ≤ N₀(𝔸)`, for the radical lattice
  `N₀(F) ∩ U'(𝔸)` and for `N_(t+1)(F) × N_(r+1)(F)`. Each is Haar measure divided by the mass of
  the Library's chosen fundamental domain, so each quotient has total mass one.
- `openProd F r t : Radical × LeviPart ≃ₜ N₀(𝔸)`, `(Y, m) ↦ u'(Y) diag(m)` (`openProd_apply`),
  is the Library's `LeftCosetSpace.Semidirect.prodHomeomorph` for the split extension.
- `haarH_eq_map_prod` (**normalized Haar measure in the open-cell coordinates**):
  `haarH = (haarN × haarM).map openProd`. This is the Library's
  `LeftCosetSpace.Semidirect.semidirectNormalizedHaar`, with the compatibility of `leviHom` and
  `projHom` with the rational points and the two finite covolumes above.
