# Order of the inertia group equals the ramification index for complete DVFs

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.ValuedGalois`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite separable extension of complete discretely valued fields (`base : CompleteDVF K`, `target : CompleteDVF L`, the target valuation extending the base one), and let `G` be a finite group acting on the valuation ring `O_L` as a Galois group of `O_L` over `O_K` (`IsGaloisGroup`).

- `card_inertia_eq_ramificationIndex_of_finite_separable`: if moreover the residue extension is separable and the scalar tower `O_K → O_L → L` holds, the ideal-theoretic inertia group of the maximal ideal of `O_L` (elements with `σx − x ∈ 𝔪_L` for all `x`) has order equal to the library's ramification index `ramificationIndex base.toDVF target.toDVF`.

The proof shows that `O_L` is finite and torsion-free over `O_K` with `𝔪_L` over `𝔪_K`, applies the Dedekind-layer formula `|I_P| = e` for the ideal ramification index, and identifies that index with the valuation-theoretic one.

The residue extension is assumed separable, and `G` is an abstract finite group acting on `O_L`, not necessarily `Gal(L/K)`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Dedekind/ValuedGalois.lean`: the Lean file is the source byte for byte (SHA-256 `aad3a545681f015e09292180a48e92078397e136124643946f169a05247471f9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
