# The valuation ring as integral closure under unique extension

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.UniqueExtensionIntegralClosure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension with group G, with discrete valuations `base` on K and `target` on L (the library's `DVF` structures), `target` extending `base`, and valuation rings O_K and O_L. The file proves, without completeness or a Henselian hypothesis, that if the valuation of K extends uniquely to L, then O_L is the integral closure of O_K in L and is a finite O_K-module.

## Definitions and results

- `integralOrbitPolynomial huniq a`: for a in O_L, the product of X − σ(a) over σ ∈ G, a polynomial over O_L. Every factor has coefficients in O_L because G preserves O_L under unique extension.
- `integralOrbitPolynomial_monic` and `integralOrbitPolynomial_map_valuationSubringAut`: the polynomial is monic and invariant under G.
- `integralOrbitPolynomial_coeff_mem_range`: each coefficient comes from O_K. It is fixed by G, so it lies in K, and it is integral for the valuation.
- `target_valuationSubring_element_isIntegral_of_uniqueExtension` and `target_valuationSubring_isIntegral_of_uniqueExtension`: every element of O_L is integral over O_K, since it is a root of the descended monic polynomial.
- `target_valuationSubring_isIntegralClosure_of_uniqueExtension`: O_L is the integral closure of O_K in L.
- `target_valuationSubring_moduleFinite_of_uniqueExtension`: O_L is a finite O_K-module. This uses that O_K is noetherian, together with a library result on integral closures of valuation rings.

## Watch for

Unique extension is the explicit hypothesis `huniq : DVF.HasUniqueValuationExtension base target`. The Galois hypothesis is used to descend the coefficients: monicity and invariance are stated for finite L/K, and the coefficient descent, integrality, integral-closure and finiteness results only for finite Galois L/K. According to the file's comment, the finiteness statement replaces an input that formerly relied on completeness in the proof of monogeneity.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/UniqueExtensionIntegralClosure.lean`: the Lean file is the source byte for byte (SHA-256 `44fd81a9e22fe39dbdb27b9362a6c826ab0649548e95379e22a46927b13d251b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
