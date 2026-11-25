# Valuative extensions of nonarchimedean local fields

`Langlands/GaloisCohomology/Local/Arithmetic/Extension.lean`, namespace `Langlands.GaloisCohomology.Local`.

Basic facts on an extension `L/K` of fields with valuative relations extending each other
(`ValuativeExtension K L`): the valuation of `L` extends that of `K` in Mathlib's sense, the rings
of integers form an extension `𝒪[K] → 𝒪[L]`, and for nonarchimedean local fields the inclusion
`K → L` is continuous, so `L` is a topological `K`-module.

## Declarations

- Instance `valuation_hasExtension K L`: `(valuation K).HasExtension (valuation L)`.
- `coe_algebraMap_integer`, `algebraMap_integer_injective`: the map `𝒪[K] → 𝒪[L]`.
- `algebraMap_mem_integer_iff`: `a ∈ K` is integral in `L` iff it is integral in `K`.
- `continuous_algebraMap K L`: `K → L` is continuous; instance `continuousSMul`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/LocalFields/Interface.lean`, with the names unchanged.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

## References

- J.-P. Serre, *Local Fields*, chapter II, §2, Proposition 3 (the integral closure of the valuation
  ring of a complete field in a finite extension is a discrete valuation ring, free of rank `[L :
  K]`, and the extension is complete), p. 28.
