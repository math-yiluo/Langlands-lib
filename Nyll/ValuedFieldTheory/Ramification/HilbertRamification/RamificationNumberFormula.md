# The sum formula for the Herbrand function

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumberFormula`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension with group G, with discrete valuations `base` on K and `target` on L (the library's `DVF` structures), `target` extending `base`, and separable residue extension. Write i(σ) for `intrinsicRamificationNumberOfUniqueExtension`, the ramification number in ℕ∞, and G_0 for the inertia group, the level-0 group of `lowerRamificationFiltrationOfUniqueExtension`. The file proves, without completeness, the classical sum formula for the Herbrand function in terms of ramification numbers.

## Main result

`herbrandFunctionOfUniqueExtension_eq_intrinsicRamificationNumber_sum`: for every real s ≥ −1,

η(s) = (1/|G_0|) · (sum over σ ∈ G of min(i(σ), s + 1)) − 1,

where `truncateENatAtDVF` gives min(i, s + 1), and s + 1 itself when i = ∞.

## Helper results

For a natural number m with m ≤ s ≤ m + 1 and σ in G_0, `truncate_intrinsicRamificationNumberOfUniqueExtension_eq_intrinsic_summand` expresses min(i(σ), s + 1) as 1 plus the truncated lower depth of σ at m, plus s − m when σ lies in the lower group at level m + 1. Elements outside G_0 contribute 0 for s ≥ −1, so the sum over G equals the sum over G_0. That sum is |G_0| plus the sum of the truncated depths plus (s − m) times the order of the lower group at level m + 1.

## Proof

Each statement applies an abstract result about antitone filtrations and depth functions, here `herbrandFunction_eq_depth_sum_of_mem` and its companions. The only input from the field is the criterion that σ lies in G_n exactly when i(σ) ≥ n + 1.

## Watch for

- Unique extension of the valuation is the explicit hypothesis `huniq : DVF.HasUniqueValuationExtension base target`. Separability of the residue extension is a standing assumption.
- No generator of the valuation ring appears in the statements: one is chosen inside the definition of i.
- The formula is stated only for s ≥ −1.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationNumberFormula.lean`: the Lean file is the source byte for byte (SHA-256 `2748a9364a26d90333d45f0ae8028f333b12914c57ae31f9027273f641c0e67c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
