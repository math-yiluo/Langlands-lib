# Ramification numbers as a nonarchimedean depth

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an extension with Galois group G, with discrete valuations `base` on K and `target` on L (the library's `DVF` structures), `target` extending `base`, and valuation rings O_K and O_L. For a in O_L, the ramification number i_a(σ) is the additive valuation of σ(a) − a in O_L, a value in ℕ∞. The file shows that, at a generator of O_L over O_K, these numbers satisfy the axioms of the library's abstract nonarchimedean depth on G.

## Results

- `addVal_valuationSubringAutOfUniqueExtension`: every σ in G preserves the additive valuation of O_L.
- `valuationSubringAutOfUniqueExtension_mul_sub_eq`: στ(a) − a = σ(τ(a) − a) + (σ(a) − a).
- `ramificationNumberOfUniqueExtension_mul_ge_min`: i_a(στ) ≥ min(i_a(σ), i_a(τ)). `ramificationNumberOfUniqueExtension_mul_eq_min_of_ne` gives equality when i_a(σ) ≠ i_a(τ). Both hold for any a.
- `ramificationNumberOfUniqueExtension_eq_top_iff`: if a generates O_L as an O_K-algebra, then i_a(σ) = ∞ exactly when σ = 1.
- `ramificationNumberOfUniqueExtension_conj`: for a generator a, i_a(τστ⁻¹) = i_a(σ).
- `ramificationNumberDepthOfUniqueExtension`: the `NonarchimedeanDepth` on G whose depth is `intrinsicRamificationNumberOfUniqueExtension`, the ramification number at a chosen generator. A simp lemma unfolds its depth.

## Proof

The product rule follows from the displacement identity and the ultrametric inequality for the additive valuation. If σ fixes a generator, it fixes O_L and hence its fraction field L. Conjugation moves a to τ⁻¹(a), which is again a generator, and an earlier result says the ramification number does not depend on the generator chosen.

## Watch for

- Unique extension of the valuation is the explicit hypothesis `huniq : DVF.HasUniqueValuationExtension base target` throughout.
- The depth structure further assumes L/K finite Galois and the residue extension separable, which supply the chosen generator.
- `NonarchimedeanDepth` is the library's own abstraction of the function σ ↦ i_G(σ), not a Mathlib notion.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationDepth.lean`: the Lean file is the source byte for byte (SHA-256 `c277785733231ef564d8dcc4ccce7fc308fd706eae1503a2677d17c769f06939`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
