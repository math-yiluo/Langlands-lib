# The first-column line subgroup

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. In Jacquet–Shalika
1985, §4.4 (formula (11), printed page 328) the averaging group is `K_(r-2)(f)`, the integral
matrices whose last row is `(0, …, 0, *)` modulo `𝔭^f`. In the Library's dual coordinates the
corresponding group is its image under `A ↦ w ᵗA⁻¹ w`, the integral matrices whose first column
is `(*, 0, …, 0)` modulo `𝔭^f`. This module constructs that group.

- `firstColumnLine R n`: over any commutative ring, the invertible matrices whose first column
  is a multiple of `e_0` form a subgroup. Closure under inverses: from `(g⁻¹ g)_(j,0) = δ_(j,0)`
  and the first-column condition, `g⁻¹_(j,0) g_(0,0) = δ_(j,0)`; so `g_(0,0)` is a unit and
  `g⁻¹_(j,0) = 0` for `j ≠ 0`.
- `integralFirstColumn n I`: its preimage under reduction modulo an ideal `I`;
  `mem_integralFirstColumn` gives the entry condition `g_(j,0) ∈ I` for `j ≠ 0`;
  `integralPrincipalCongruence_le_integralFirstColumn`: it contains the principal congruence
  group of `I`.
- `firstColumnCongruence O n I`: the image in the field group under entrywise inclusion of the
  integer ring `O` (the same pattern as the published `Conductor.congruenceSubgroup`).
  `mem_firstColumnCongruence`: `g` and `g⁻¹` are integral and `g_(j,0) ∈ I` for `j ≠ 0`.
  It contains the published principal congruence subgroup and is contained in the integral
  subgroup.
- `firstColumnOpenSubgroup F n f` (`K⁰(f)`): over a nonarchimedean local field, at `I = 𝔭^f`, it
  is open because it contains the published open `principalLevelOpenSubgroup F n f`;
  `isCompact_firstColumnOpenSubgroup`: it is a closed subset of the compact integral group.
