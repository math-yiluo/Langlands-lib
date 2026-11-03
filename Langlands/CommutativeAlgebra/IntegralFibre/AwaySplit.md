# Local splitting over a smooth localization

This module is part of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
Write `B = Localization.Away s` for `s : S`. The module proves that `B ⊗[R] S` is locally split
over `B` when `B` is smooth over `R` and `Ω[B⁄R]` is free.

## Definitions

- `diagSection s : B ⊗[R] S →ₐ[B] B`: the diagonal section `b ⊗ x ↦ b x̄`.
- `diagDiff s : B ⊗[R] S →ₗ[B] Ω[B⁄R]`: the map `b ⊗ x ↦ b • d x̄`.
- `diagDelta s x = 1 ⊗ x - x̄ ⊗ 1`: an element of the kernel `J` of the diagonal section.
- `diagDer s : Derivation R S J.Cotangent`: the derivation `x ↦ [diagDelta s x]`.
- `diagConormal s : Ω[B⁄R] →ₗ[B] J.Cotangent`: the map with `d x̄ ↦ [diagDelta s x]`.
- `diagDim`, `diagBasis`, `diagCoord`, `diagT`: assuming `Ω[B⁄R]` is free and finite, a basis
  of `Ω[B⁄R]`, the resulting coordinate derivation, and elements `diagT s i ∈ J` whose
  differentials are the basis vectors.

## Statements

- `diagDiff_mul`: `diagDiff s` is a derivation at `diagSection s`.
- `diagDiff_surjective`: `diagDiff s` is surjective. It hits `map (d x)` for every `x`, and
  `Ω[B⁄R]` is the localization of `Ω[S⁄R]` (`KaehlerDifferential.isLocalizedModule_map`).
- `eq_sum_diagDelta`: every element of `J` is a `B`-combination of elements `diagDelta s x`.
- `toCotangent_eq_diagConormal`: for `j ∈ J`, `[j] = diagConormal s (diagDiff s j)`.
- `mem_sq_of_diagDiff_eq_zero`: if `j ∈ J` and `diagDiff s j = 0`, then `j ∈ J^2`.
- `diagCoord_mul`, `diagSection_diagT`, `diagCoord_diagT`: `diagT s i ∈ J`, and
  `diagCoord s (diagT s i)` is the `i`-th unit vector.
- `ker_diagSection_le`: `J ≤ span (range (diagT s)) ⊔ J^2`.
- `formallySmooth_away_one_tmul`: if `B` is formally smooth over `R`, then
  `Localization.Away (1 ⊗ s)` is formally smooth over `B`. It is isomorphic to `B ⊗[R] B`
  (`IsLocalization.tensorProductEquivOfMapIncludeRight`).
- `locallySplit_away`: let `S` be finitely presented and flat over `R`, with `K ⊗[R] S` a domain
  for every field `K` over `R`. Suppose `B` is smooth over `R` and `Ω[B⁄R]` is free. Then
  `LocallySplit B (B ⊗[R] S)`.

## Proofs

The conormal comparison comes from the derivation `diagDer`, through
`Derivation.liftKaehlerDifferential` and `IsLocalizedModule.lift`. The lift exists because `s`
acts invertibly on `J/J^2`. The comparison is `B`-linear by
`LinearMap.extendScalarsOfIsLocalization`.

For `ker_diagSection_le`, subtract from `j ∈ J` the combination `∑ (diagCoord s j)ᵢ • diagT s i`.
The difference has zero differential, so it lies in `J^2`.

For `locallySplit_away`, the element `1 ⊗ s` has unit image under the section, and its
localization is formally smooth. So `theta_injective_of_formallySmooth` makes every Taylor map
injective. `exists_noetherianModel` supplies a Noetherian model of `B ⊗[R] S` with these
coordinates. Each fibre `κ(P) ⊗[B] (B ⊗[R] S) ≃ κ(P) ⊗[R] S` is a domain. Then
`locallySplit_of_noetherianModel` concludes.

## Provenance

This is internal to the 05FT proof, written by Worker 281. The identification of the conormal
module of the diagonal with `Ω` is standard; compare Stacks Tag 00RW.
