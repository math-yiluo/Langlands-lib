# Renormalizing shifts on left coset spaces

Module `Langlands.Analysis.CosetSpaceShift`. Generic measure theory for a subgroup `H` of a
group `A` with a σ-algebra; no topology is used.

## Definitions

- `Space H` is the left coset space `H \ A`, the quotient of `A` by
  `QuotientGroup.rightRel H` (`a ~ b ↔ b a⁻¹ ∈ H`), and `mk H : A → Space H` the quotient
  map (`mk_eq_mk_iff`, `mk_mul`).
- `Space H` carries the quotient σ-algebra `MeasurableSpace.map (mk H)`: a set is measurable
  when its preimage in `A` is measurable. Hence `mk H` is measurable, and a function on
  `Space H` is measurable as soon as its composition with `mk H` is (`measurable_of_comp`).
- `lift H φ hφ` is the function on `Space H` induced by an `H`-left-invariant function `φ`
  (`lift_mk`, `measurable_lift`).
- `shift H a ha` is the map `H g ↦ H a g` induced by left translation by a point `a` with
  `a H a⁻¹ ⊆ H` (`shift_mk`, `measurable_shift`).
- `IsInvariantSet H B`: the set `B ⊆ A` is a union of cosets `H g`. Preimages of sets of
  `Space H` are such sets (`isInvariantSet_preimage_mk`).

## Results

- `lintegral_lift`, `eLpNorm_lift`, `memLp_lift_iff`: integrals, `Lᵖ` seminorms and `Lᵖ`
  membership of a descended measurable function against the pushforward `map (mk H) ν`
  equal those of the function against `ν` (change of variables `lintegral_map`,
  `eLpNorm_map_measure`, `memLp_map_measure_iff`). `restrict_map_mk` identifies the
  restriction of the pushforward to a measurable set `s` with the pushforward of the
  restriction to `mk H ⁻¹' s`.
- `map_shift_map_mk`: if `ν((a ·)⁻¹ B) = k ν(B)` for every measurable `H`-invariant `B`, then
  `map (shift H a ha) (map (mk H) ν) = k • map (mk H) ν`. The preimage under `mk H` of the
  preimage of `s` under the shift is the preimage under left translation by `a` of the
  invariant set `mk H ⁻¹' s`.
- `renormalizingShift`: under that hypothesis with `k = c²`, `c > 0`, and for a measurable
  `H`-invariant real function `ht` on `A` with `ht(a g) = ht(g) + 1`, the data
  `(shift H a ha, lift H ht, c)` form an `L2RenormalizingShift` of `map (mk H) ν` (module
  `Langlands.Analysis.L2SlabRecurrence`).

## Provenance

Derived measure-theoretic infrastructure for the renormalizing transformations of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234, §7.5, p. 218 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`): there, functions on
`P₀(F) U(𝔸) \ G(𝔸)` are translated on the left by points `a_α` of split components, which
act on that quotient but not on `P₀(F) \ G(𝔸)`. Passing to the coset space makes these
translations point maps, so that the slab estimates of `L2SlabRecurrence` and
`L2IndependentSlabs` apply.
