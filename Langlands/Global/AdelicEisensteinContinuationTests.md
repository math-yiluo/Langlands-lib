# Norm-one Levi tests of a function-valued meromorphic continuation

Module `Langlands.Global.AdelicEisensteinContinuationTests` proves
`StandardParabolicFamily.exists_openDense_continuation_tests`.

Let `E : ℂⁿ → (G(𝔸) → ℂ)` have local function-valued meromorphic presentations in the
uniform-growth Fréchet spaces `UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L`,
in the form of the conclusion of `EisensteinMeromorphicContinuationStatement`. That is,
near every point there are an open `W`, a stage `(R, L)` and a meromorphic map
`f : W → 𝔉^R_L` with domain `D`, such that for `s ∈ D` the function underlying `f s` is
`E s` and `E s` is automorphic on `G(F) \ G(𝔸)`. Assume that every Levi cusp form `ψ` of a
standard family has integrable weighted majorants (`HasLeviPairingMajorant`) at every `g`
and every growth exponent.

The theorem gives one open dense `U ⊆ ℂⁿ` with three properties:

1. every point evaluation `s ↦ E s g` is meromorphic with domain `U`;
2. `E s` is automorphic for every `s ∈ U`;
3. for every standard `J`, every Levi cusp form `ψ` on `M_J` and every `g`, the scalar
   function `s ↦ (C_J E s (· g), ψ)` is meromorphic with domain `U`.

## Proof

Choose the local presentations at every point, and let `U` be the union of their domains.
On each piece, point evaluation (`UniformGrowthFrechetSpace.evaluation`) and the Levi
pairing of the constant term (`constantTermLeviPairingCLM`) are continuous linear forms on
the growth stage. The latter is continuous because of the majorant. Composition with a
continuous linear form preserves meromorphy (`IsMeromorphicOn.comp_continuousLinearMap`),
and on the local domain the composite agrees with the scalar function of `E`.
`isMeromorphicOn_of_openCover` glues the pieces to meromorphy on `U`. Automorphy on `U` is
part of the local data.

This is a derived step of the far-region comparison in Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series* (2024), §8.6, using the Fréchet form of their corollary
in §8.6 and the pairing (6.8).
