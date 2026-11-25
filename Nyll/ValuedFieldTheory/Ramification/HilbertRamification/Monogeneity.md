# Monogeneity of the valuation ring over a noncomplete discretely valued field

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Monogeneity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an extension with discrete valuations `base` on K and `target` on L (the library's `DVF` structures), `target` extending `base`, and write O_K, O_L for the valuation rings and m_K, m_L for their maximal ideals. The file proves, without completeness, that O_L = O_K[a] for a single element a when L/K is finite Galois, the valuation of K extends uniquely to L and the residue extension is separable.

## Results

- `map_maximalIdeal_eq_pow_ramificationIdx_dvf`: m_K·O_L = m_L^e, with e Mathlib's `Ideal.ramificationIdx'`.
- `residueField_finiteDimensional_of_moduleFinite_dvf`: if O_L is a finite O_K-module, the residue extension is finite.
- Polynomial helpers: residue polynomials lift to O_K, and reduction commutes with extending coefficients. A root modulo m_L gives a value in m_L, and a nonzero reduced derivative gives a unit derivative.
- `exists_residue_eq_polynomial_eval_isUniformizer_dvf`: if P(a) ∈ m_L and P′(a) is a unit, then some y with the same residue as a has P(y) a uniformizer: y = a if P(a) ∉ m_L², and y = a + π otherwise.
- `exists_mem_adjoin_sub_mem_maximalIdeal_pow_dvf`: if the residue extension is algebraic and generated as a field by the residue of a, and P(a) is a uniformizer for some P over O_K, then every element of O_L is congruent modulo m_Lⁿ to an element of O_K[a], for every n.
- `exists_primitive_residue_lift_polynomial_uniformizer_dvf`: for a finite separable residue extension, there are a in O_L whose residue is a primitive element and P over O_K with P(a) a uniformizer and P′(a) a unit. The statement does not say how P arises; the proof takes a lift of the minimal polynomial of the primitive element.
- `exists_valuationSubring_generator_data_of_uniqueExtension`: under unique extension and residue separability, such P and a exist with, in addition, O_K[a] = O_L.
- `exists_valuationSubring_adjoin_eq_top_of_uniqueExtension`: the bare statement that O_L = O_K[a] for some a.

## Proof

Unique extension makes O_L a finite O_K-module (from an earlier file), so the residue extension is finite. A primitive residue element and its minimal polynomial are lifted, and the lift is adjusted so that P(a) is a uniformizer. Approximation modulo m_L^e = m_K·O_L then gives O_L = O_K[a] + m_K·O_L, and Nakayama's lemma gives O_L = O_K[a].

## Watch for

- Unique extension is not derived from completeness: it is the explicit hypothesis `huniq : DVF.HasUniqueValuationExtension base target`.
- The two final theorems also carry the section's assumptions that L/K is finite and Galois, and both assume the residue extension separable. The helper lemmas drop the finiteness and Galois assumptions.
- `DVF` and its residue fields are the library's own structures, not Mathlib's.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Monogeneity.lean`: the Lean file is the source byte for byte (SHA-256 `de74d0a26aea1a5518dd3c6d7bf37942d8ab629f2ded96439b26289d1a779956`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
