# Ramification numbers over a general discretely valued field

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an extension with Galois group G, with discrete valuations `base` on K and `target` on L (the library's `DVF` structures), `target` extending `base`, valuation rings O_K and O_L, and maximal ideal m_L. The file defines the ramification number i(σ) of σ in G without completeness, as the additive valuation of σ(a) − a in O_L for a generator a of O_L over O_K. The generator is chosen inside the definition, so later statements carry no generator hypothesis.

## Definitions

- `valuationSubringDisplacementSubalgebraOfUniqueExtension huniq n σ`: the elements a of O_L with σ(a) − a ∈ m_Lⁿ. They form an O_K-subalgebra.
- `ramificationNumberOfUniqueExtension huniq a σ`: the additive valuation of σ(a) − a, in ℕ∞, for an arbitrary a in O_L.
- `chosenRamificationGeneratorOfUniqueExtension`: a generator of O_L as an O_K-algebra, chosen from the monogeneity theorem.
- `intrinsicRamificationNumberOfUniqueExtension huniq σ`: the ramification number at that chosen generator.

## Results

- `valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin`: if σ(a) − a ∈ m_Lⁿ, the same holds for every element of O_K[a].
- `natCast_le_ramificationNumberOfUniqueExtension_iff`: n ≤ i_a(σ) exactly when σ(a) − a ∈ m_Lⁿ. The identity has value ∞.
- `ramificationNumberOfUniqueExtension_eq_of_adjoin_eq_top`: any two generators of O_L over O_K give the same ramification number.
- `mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge`: σ lies in the lower ramification group G_n exactly when i(σ) ≥ n + 1.

## Watch for

- Unique extension of the valuation is the explicit hypothesis `huniq : DVF.HasUniqueValuationExtension base target`.
- The chosen generator and `intrinsicRamificationNumberOfUniqueExtension` also need L/K finite Galois and the residue extension separable. `ramificationNumberOfUniqueExtension` needs neither.
- The number is normalized by the valuation of L, so G_n corresponds to i(σ) ≥ n + 1.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationNumber.lean`: the Lean file is the source byte for byte (SHA-256 `4667b996e8319c35e04e57865788af63fd6ff91562c55f4a4dffef4b4dd72dfd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
