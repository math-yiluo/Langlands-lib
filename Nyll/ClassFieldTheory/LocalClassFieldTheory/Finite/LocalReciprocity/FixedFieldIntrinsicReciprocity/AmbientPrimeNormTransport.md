# Transport of prime units and norms, and the norm-residue symbol on norms of primes

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file evaluates the abstract fixed-field norm-residue symbol over a nonarchimedean local field `K` on norms of prime elements. To do so it moves units of valuation one and norm classes along ring isomorphisms, and identifies the class formation's relative norms with field norms.

## Transport lemmas

- `exists_valuationOne_unit_of_ringEquiv`: if `φ : L ≃+* M` is a ring isomorphism of nonarchimedean local fields that preserves valuation subrings (hypothesis `hmem`), some unit `p` of `L` has `valuationMap` equal to 1 in `L` and `φ p` has `valuationMap` 1 in `M`. `chosenValuationOneUnitOfRingEquiv` picks such a unit by `Classical.choose` (lemmas `_source`, `_target`).
- `valuationSubring_mem_iff_of_separableClosureRingEquiv`: if finite separable extensions `L/F`, `M/K` of nonarchimedean local fields, with compatible valuations, embed into the separable closures, `ψ` is a ring isomorphism of those closures matching their selected valuation subrings, and `φ : L ≃+* M` is compatible with `ψ`, then `φ` preserves valuation subrings.
- `normUnits_mapEquiv` and `normClass_mapEquiv`: norms of units and equality of norm classes commute with ring isomorphisms of base and extension that are compatible with the algebra maps.

## Abstract norms and prime elements

- `localHenselianValuation_isPrimeElement_abstractFixedField`: for a finite abstract field `H` whose fixed field carries its spectral local-field structure, a unit of valuation one in that fixed field is a prime element for `localHenselianValuation K` at `H`.
- `relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit` and `relativeNorm_preimage_abstractRelativeFixedFieldUnit`: the class formation's `relativeNorm` of a fixed-field unit corresponds to its field norm `normUnits`.

## Evaluation on norms of primes

- `abstractFixedFieldNormResidueSymbol_eq_of_primeNorm`: let `J ≤ H` give a finite normal extension and `σ` be a Frobenius element of `localResidueDatum K` for it, with Frobenius fixed field `S`. If a unit `p` of the relative fixed field of `S` is a prime element for `localHenselianValuation K` and `x` is its norm, then the norm-residue symbol of `x` is the image in the abelianized Galois group of the Frobenius restriction of `σ`.
- `abstractFixedFieldNormResidueSymbol_eq_of_transportedValuationOneUnit`: the same value at `phiF` of the norm from `L` to `F` of the chosen valuation-one unit, for `L/F` finite and ring isomorphisms `phiF`, `phi` of `F`, `L` onto the fixed field of `H` and that relative fixed field, commuting with the algebra maps (`_hcomm`), `phi` preserving valuation subrings (`hmem`).

## Points to watch

- The last theorem assumes, as hypothesis `_hprime`, that the transported unit is a prime element, and takes the local-field structure on the relative fixed field as instance arguments; neither is derived there.
- "Valuation one" means `valuationMap` equals 1; in the library's normalization this holds for the inverse of a uniformizer.
- Frobenius elements, Frobenius fixed fields, `relativeNorm` and `localHenselianValuation` are the library's class-formation notions; the fields live in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean`: the Lean file is the source byte for byte (SHA-256 `e3c7e4384eab3a898e52da4d18715adba2520194c5e4333b873bcc7402fd5fc7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
