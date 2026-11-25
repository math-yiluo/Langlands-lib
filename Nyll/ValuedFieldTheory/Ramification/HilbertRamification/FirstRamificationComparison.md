# G₀ is the inertia group and G₁ is Hilbert's ramification group

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FirstRamificationComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library has two conventions for ramification. Lower ramification groups of discretely valued fields are given by congruences for the action on the valuation ring (`σ ∈ G₀` iff `σa − a` lies in the maximal ideal for every `a`), and the higher principal units `U^(n)` of that theory are units of the valuation ring. Hilbert's ramification group is defined in the valuation-subring theory through the principal-unit subgroup of the field units `Lˣ`. For a finite Galois extension of complete discretely valued fields with separable residue extension, the file shows that the lower group `G₀` is the inertia group and `G₁` is Hilbert's ramification group.

## Main results

- `mem_dvfHigherPrincipalUnitGroup_one_iff_principalUnitGroup`: a unit of the valuation ring lies in `U^(1)` iff its image in `Lˣ` is a principal unit in Hilbert's sense.
- `coe_dvfUniformizerQuotientUnit_eq_automorphismUnitQuotient`: the unit `σ(π)/π` of the DVF theory equals Hilbert's quotient `σ(π)/π` in `Lˣ`.
- `inertia_forall_automorphismUnitQuotient_mem_principal_iff_uniformizer` (any discretely valued `L`): for an inertia element `σ`, `σy/y` is a principal unit for every `y ∈ Lˣ` iff this holds for one uniformizer `π`.
- `mem_lowerRamificationGroup_zero_iff_completeDVF_inertiaGroup` (complete DVFs, `L/K` finite separable): `σ ∈ G₀` iff `σ` is in the inertia group of the complete-DVF file.
- `mem_lowerRamificationGroup_one_of_uniformizerQuotient_mem` (`L/K` finite Galois, separable residue extension): if `σ ∈ G₀` and `σ(π)/π ∈ U^(1)`, then `σ ∈ G₁`.
- `lowerRamificationGroup_one_eq_hilbertRamificationGroup` (complete DVFs, `L/K` finite Galois, separable residue extension): `G₁` is the preimage of Hilbert's ramification group under `Gal(L/K) ≃ D`.

## Proofs

Nonzero elements of the valuation ring factor as a power of `π` times a unit (other elements are treated through their inverses), and for `σ` in inertia `σu/u` is a principal unit for every unit `u`, so the condition at `π` gives it at every `y`. The step from `σ(π)/π ∈ U^(1)` to `σ ∈ G₁` uses injectivity of the uniformizer map on `G₀/G₁`, which needs a separable residue extension.

## Points to watch

- Unique extension of the valuation (`huniq`) is an explicit hypothesis even in the complete case.
- The identification of `G₁` is proved only for a separable residue extension; the lower groups are indexed by real numbers, with `G₀`, `G₁` at `0` and `1`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FirstRamificationComparison.lean`: the Lean file is the source byte for byte (SHA-256 `3c797528368915ca71b62cd7f9a2da73c8a3ba6bc4ea0d6f1e9707d763943e27`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
