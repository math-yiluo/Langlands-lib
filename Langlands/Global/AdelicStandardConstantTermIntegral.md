# Constant terms along standard unipotent radicals

Module `Langlands.Global.AdelicStandardConstantTermIntegral`, namespace
`Langlands.Global.StandardConstantTerm`. It instantiates
`Langlands.Global.AdelicConstantTermAverage` for `Λ = P₀(F)` and the standard unipotent
radicals. The Library module `Langlands.Global.AdelicStandardConstantTerm` is a separate
module. It treats complex constant terms of continuous functions along nested standard
parabolics of a `StandardParabolicFamily`, and this module neither imports nor changes it.

## Setting

`G` is connected reductive over a number field `F` (affine, locally of finite type), `i : T → G`
is a maximal split torus, `ν` is a generic cocharacter and `J ⊆ Δ₀ = simpleRelativeRoots i ν`.
`standardParabolic i ν J` (`P_J`) and `standardUnipotent i ν J` (`U_J`) are the Library's
standard subgroup functors.

## Definitions and structural facts

- `minimalParabolicImage F G i ν` (`Λ₀`) is the image in `G(𝔸)` of the rational points
  of `P₀ = P_∅`. It lies in the principal subgroup `G(F)` (`minimalParabolicImage_le`), so it is
  discrete (`isDiscrete_minimalParabolicImage`).
- `standardUnipotent_isNormalizedBy_standardParabolic`: `P_J` normalizes `U_J` on every test
  scheme. Both are intersections over the standard cocharacters `ζ` of `J` of the dynamic groups
  `P(ζ)` and `U(ζ)`, and `P(ζ)` normalizes `U(ζ)` (`Dynamic.conj_mem_unipotent`).
- `smooth_standardUnipotentScheme`, `connectedSpace_standardUnipotentScheme`: the representing
  scheme of `U_J` is smooth and connected. By `standardCocharacter`, `U_J` equals the dynamic
  unipotent group of one standard cocharacter; then the dynamic smoothness and connectedness
  theorems apply.
- `isClosed_adelicPoints_standardUnipotent` (`U_J(𝔸)` is closed in `G(𝔸)`) and
  `compactSpace_standardUnipotent` (`U_J(F) \ U_J(𝔸)` is compact). These use the closed
  immersion `Standard.unipotentHom`, unipotence (`isUnipotent_standardUnipotentScheme`) and the
  Library's `compactSpace_rationalQuotient_range_unipotent`.
- `standardUnipotent_le_minimalParabolic` (`U_J ≤ P₀`) and
  `minimalParabolic_le_standardParabolic` (`P₀ ≤ P_J`), from `standardParabolicOrder`.
- `rationalSubgroup_standardUnipotent_le` (`U_J(F) ⊆ Λ₀`),
  `conj_rationalSubgroup_standardUnipotent` (`Λ₀` normalizes `U_J(F)`) and
  `conj_adelicPoints_standardUnipotent` (`Λ₀` normalizes `U_J(𝔸)`).

## Statement

`StandardConstantTermIntegralStatement`, proved by `standardConstantTermIntegral`. For every
`J ⊆ Δ₀` and every measurable `f : G(𝔸) → [0, ∞]` that is left invariant under `Λ₀ = P₀(F)`:

1. the nonnegative constant term `lowerConstantTerm F G U_J f` (the integral of `f(u g)` over
   `U_J(F) \ U_J(𝔸)` for the mass-one quotient measure) is left `Λ₀`-invariant;
2. its integral over the Library's Borel fundamental domain of `Λ₀` equals that of `f`.

This is the measure identity behind the constant-term projections `CT_P` on
`P₀(F) \ G(𝔸)` in Bernstein–Lapid, J. Amer. Math. Soc. 37 (2024), §7.3, p.214, for every
standard parabolic `P = P_J`. For the maximal parabolics of the target statement
`UniformGrowthLocalFinitenessStatement`, `SubgroupFunctor.range (u α) = U_{Δ₀ ∖ {α}}`, so this
constant term is the one integrated by the Library's `subgroupConstantTerm F (u α)`.

## Proof

The structural facts above discharge the hypotheses of
`ConstantTermAverage.lowerConstantTerm_mul_left` and
`ConstantTermAverage.setLIntegral_lowerConstantTerm` for `U = U_J` and `Λ = Λ₀`.

## Scope

The module does not prove the composition rule `CT_R CT_Q = CT_{R ∩ Q}` or the bounded `L²`
operators on the weighted Siegel domain space, and it makes no statement about local finiteness.
