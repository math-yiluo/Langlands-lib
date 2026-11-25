# Topology of a complete DVF with range-restricted valuation

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a complete discretely valued field `F : CompleteDVF K` of the library, the valuation restricted to its multiplicative range (`CompleteDVF.mrangeRestrict F`) is rank one. The file equips `K` with the valued and normed-field structures of this valuation and shows that the valuation ring is complete, compact when the residue field is finite, and that `K` is then proper and complete.

## Definitions

- `mrangeRestrictValued F`: the `Valued` structure on `K` given by the restricted valuation; `mrangeRestrictValued_rankOne F` its rank-one structure.
- `mrangeRestrict_nontriviallyNormedField F`: the resulting nontrivially normed field structure on `K`.
- `mrangeRestrictCompleteDVF F`: a new `CompleteDVF K` whose value group is the range of `F.valuation`, built from rank-one discreteness and adic completeness of the restricted valuation.

## Results

- `mrangeRestrict_exists_uniformizer_pow_lt_unit`: for a uniformizer `π` of `F` and a unit `γ` of the range, some power `πᴺ` has restricted valuation below `γ`.
- `mem_subfield_of_mrangeRestrict_isClosed_of_forall_valuationSubring_smodEq`: if a subfield `E` of `K` is closed in this topology and an element `b` of the valuation ring is congruent, modulo every power of the maximal ideal, to an integral element of `E`, then `b ∈ E`.
- `mrangeRestrict_integer_isAdic`, `mrangeRestrict_integer_completeSpace`: the topology on the valuation ring `𝒪[K]` is the `𝓂[K]`-adic one, and `𝒪[K]` is complete.
- `mrangeRestrict_integer_compactSpace_of_residueField_finite`: with finite residue field, `𝒪[K]` is compact.
- `mrangeRestrict_properSpace_of_residueField_finite`, `mrangeRestrict_completeSpace_of_residueField_finite`: with finite residue field, `K` is proper, hence complete.

## Proofs

Cofinality of uniformizer powers comes from the range's unit group being cyclic, hence Archimedean. Completeness of `𝒪[K]` combines the adic description of the topology with adic completeness from the range-restriction file. Compactness applies Mathlib's criterion (complete, discrete valuation ring, finite residue field), and properness Mathlib's equivalence with compactness of `𝒪[K]`.

## Watch for

- All structures are definitions passed by `let`/`letI` inside the statements, not instances; the results are about this particular topology on `K`.
- The closed-subfield criterion uses approximation by elements of `E` that lie in the valuation ring of `F`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/RangeRestrictedTopology.lean`: the Lean file is the source byte for byte (SHA-256 `f75b92a2fc603883d8860dbd5629211d84747ffbc7a70523a0db52682085860c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
