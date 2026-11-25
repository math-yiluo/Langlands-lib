# The stabilizer step of Krasner's lemma

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ValuationKrasner`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an extension with discrete valuations `base` on K and `target` on L (the library's `DVF` structures), `target` extending `base` uniquely, and let O_L be the valuation ring of L. The file proves the step of Krasner's argument about stabilizers, using only the additive valuation of O_L.

`valuationSubringAutOfUniqueExtension_eq_of_fixed_of_close`: let a, b be in O_L and σ in Gal(L/K) with σ(b) = b. Suppose that whenever σ(a) ≠ a, the valuation of σ(a) − a is strictly smaller than that of a − b. Then σ(a) = a.

Proof: σ preserves the additive valuation, so v(σ(a) − b) = v(a − b). The ultrametric inequality then gives v(σ(a) − a) ≥ v(a − b), a contradiction.

Watch for: this is only one step of Krasner's lemma, stated for a single K-automorphism σ of L, with no Galois or finiteness hypothesis on L/K. It does not produce a field inclusion K(a) ⊆ K(b). Unique extension of the valuation is the explicit hypothesis `huniq : DVF.HasUniqueValuationExtension base target`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean`: the Lean file is the source byte for byte (SHA-256 `68c278f2793f02b4bc81dbfe5f3c98173008981c6322299b9b6d95861c9a1ad9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
