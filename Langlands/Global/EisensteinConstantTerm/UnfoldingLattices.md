# Retractions of closed semidirect decompositions and normalized Haar measures

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingLattices`, namespace
`Langlands.Global.LeftCosetSpace`.

## Retractions

`exists_continuous_retraction`: let `i : N → H` and `j : M → H` be homomorphisms, `j` continuous
and injective, `i(N)` a closed normal subgroup of `H` meeting `j(M)` trivially, and
`H = i(N) j(M)`. If `M` is σ-compact and `H` is locally compact, there is a continuous
homomorphism `p : H → M` with `p ∘ j = id`, `p ∘ i = 1` and kernel `i(N)`. The composite
`M → H → H / i(N)` is a continuous bijective homomorphism; Mathlib's open mapping theorem
`MonoidHom.isOpenMap_of_sigmaCompact` makes it a homeomorphism, and `p` is its inverse composed
with the quotient map.

## Normalized Haar measures

For a discrete subgroup `Δ` of a locally compact second countable group `X`,
`normalizedHaar Δ hΔ` is `Measure.haar` scaled by the reciprocal of the Haar measure of the
chosen fundamental domain `fundamentalDomain Δ hΔ`. If one compact set meets every orbit of `Δ`
(`hK`, `hKcover`):

- `normalizedHaar_fundamentalDomain`: the chosen fundamental domain has mass one;
- `isHaarMeasure_normalizedHaar`, `isMulRightInvariant_normalizedHaar` (unimodularity, from the
  Library's `isMulRightInvariant_haar_of_isFiniteMeasure`), `regular_normalizedHaar`;
- `exists_cover_of_map`: a compact cover is carried along a continuous surjective homomorphism.

## Characterization and transport

- `eq_normalizedHaar`: a left invariant measure finite on compacts giving mass one to some
  measurable transversal of `Δ` is `normalizedHaar Δ hΔ`.
- `transversal_preimage`, `transversal_image`: transversals correspond under group isomorphisms
  carrying `Δ` onto `Δ'`.
- `map_normalizedHaar`, `setIntegral_fundamentalDomain_map`: under a topological group
  isomorphism `e : X ≃ₜ* Y` with `e x ∈ Δ' ↔ x ∈ Δ`, the normalized Haar measures correspond and
  `∫_{fd Δ} g (e x) = ∫_{fd Δ'} g` for left `Δ'`-invariant `g`.

## Provenance

Internal derivations from Mathlib's Haar measure uniqueness and the Library's fundamental-domain
and finite-covolume results in `LeftCosetFundamentalDomain`, `LeftCosetSemidirectFiniteVolume`
and `AdelicLeviFiniteVolume`.
