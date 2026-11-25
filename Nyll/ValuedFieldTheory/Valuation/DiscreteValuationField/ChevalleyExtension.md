# Chevalley's extension theorem and valuation rings in a field extension

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension `L / K` and a valuation `vK` on `K` (Mathlib's `Valuation`), the file proves that `vK` extends to `L` (Chevalley), and compares the valuation rings of extensions with the integral closure of `O_K` in `L`. It also collects residue-field and tower facts for Mathlib's `HasExtension`.

## Chevalley's theorem

- `HasSomeExtensionTo vK`: there is a valuation on `L`, with value group in the universe of `L`, extending `vK`.
- `exists_extension_valuationSubring`: there is a valuation subring `B` of `L` dominating `O_K` (the map `O_K → B` is local) with `B ∩ K = O_K`. `hasExtension_valuation_iff_valuationSubring_pullback` turns this into `HasExtension` for the valuation of `B`.
- `chevalley_hasSomeExtensionTo`: every valuation on `K` extends to `L`. Variants such as `chevalley_exists_extension_valuation_with_pullback_integralClosure_local_data` keep more data about one extension: exact pullback of valuation rings, containment of the integral closure, a local map `O_K → O_L`, an injective residue map.

Proof: Mathlib's theorem that a local subring of a field is dominated by a valuation ring.

## Integral closure

- `integralClosure_mem_valuationSubring_of_hasExtension`: the integral closure of `O_K` in `L` lies in the valuation ring of every extension; `algebraMap_mem_integralClosure_valuationSubring_iff`: its intersection with `K` is `O_K`.
- `mem_integralClosure_iff_forall_valuationSubring`: an element is integral over `O_K` if and only if it lies in every valuation subring of `L` containing the image of `O_K`.
- `integralClosureValuationSubringOfMemOrInv`: if the integral closure contains `z` or `z⁻¹` for each `z`, it is a valuation subring whose valuation extends `vK`.
- `valuationSubring_isIntegralClosure_iff_isIntegral`: the valuation ring of an extension is the integral closure exactly when it is integral over `O_K`; for `L / K` finite separable and `O_K` noetherian, exactly when it is a finite `O_K`-module (`valuationSubring_isIntegralClosure_iff_moduleFinite`).
- Uniqueness criteria: two extensions whose valuation rings are both integral over `O_K` (or both module-finite) have the same valuation ring and are equivalent valuations.
- `valuationSubring_eq_of_le_of_inclusion_isLocalHom` and companions: a valuation overring `S ⊇ R` with local inclusion, or with center the maximal ideal of `R`, equals `R`.

## Residue fields and towers

For any extension, `O_K → O_L` is local and the residue map is injective, with congruence criteria for residues. `hasExtension_trans`: extensions compose in a tower `K ⊆ L ⊆ M`, compatibly with the maps of valuation rings and residue fields.

## Points to watch

- Chevalley's theorem is proved for any field extension; no algebraicity is assumed.
- The dichotomy "`z` or `z⁻¹` is integral over `O_K`" is a hypothesis `hval` of all results on `integralClosureValuationSubringOfMemOrInv`; it is not proved here.
- The uniqueness criteria assume integrality or module-finiteness of each extended valuation ring; they do not prove uniqueness for Henselian or complete fields.
- Despite the namespace `DiscreteValuationField.Valuation`, no discreteness is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`: the Lean file is the source byte for byte (SHA-256 `ff36a2cef266848cf8d77f011f5fe5d2fb669ae3d7bc28c5d130f673d350e832`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
