# Uniqueness criteria for extending a Henselian discrete valuation

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be a finite extension, `base` a Henselian discretely valued field on `K` and `target` one on `L` whose valuation extends that of `base` (the library's `HenselianDVF`). The file gives sufficient conditions for the library's predicate `HenselianDVF.HasUniqueValuationExtension base target`: every valuation on `L` extending the base valuation is equivalent to that of `target`. All criteria go through the integral closure of `O_K` in `L`.

## Main results

- `integralClosureValuationSubringIntegerMapOfMemOrInv`: when the integral closure is a valuation subring `B` (hypothesis `hval`: for each `z`, `z` or `z⁻¹` is integral), the injective map `O_K → B`. For every extension of the base valuation, the center of its valuation ring on `B` contracts to `𝔪_K`; for `L / K` separable, every prime of `B` over `𝔪_K` is the maximal ideal of `B`.
- Chain of uniqueness criteria, each for `L / K` separable unless noted:
  - from `hval`, together with a condition on centers or on primes over `𝔪_K` (no separability needed for these two), or from `hval` alone (`hasUniqueValuationExtension_of_integralClosure_mem_or_inv`);
  - from the integral closure being a local ring;
  - from the fiber over `𝔪_K` having at most one prime, or from lifting idempotents of that fiber, or from the integral closure being Henselian along the kernel of the map to the fiber;
  - from the integral closure being Henselian along `𝔪_K` times the integral closure (`hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing`).
- That Henselian property holds when `O_K` is `𝔪_K`-adically complete, or only precomplete (separatedness then follows from `𝔪_K` lying in the Jacobson radical). Hence the unconditional statements `hasUniqueValuationExtension_of_finite_separable_of_base_isAdicComplete` and `hasUniqueValuationExtension_of_finite_separable_of_base_isPrecomplete`.
- `HenselianDVF.valuationSubring_eq_of_finite_separable_of_forall_isIntegral` (and the `moduleFinite` variant): if every valuation subring of `L` extending the base valuation is integral (or module-finite) over `O_K`, any two of them are equal; with `hval` as well, each equals the subring built from the integral closure.

## Proof

Under separability the integral closure is a Dedekind domain finite over `O_K`. A valuation overring whose center is the maximal ideal of `B` equals `B`. Henselian-pair or completeness assumptions make the fiber over `𝔪_K` have a single prime, so the integral closure is local and is a valuation ring.

## Points to watch

- Several statements carry as hypotheses what is the substance of a theorem: `hval` (the integral closure is a valuation ring), `hTransfer` (every module-finite `O_K`-algebra is Henselian along the extension of `𝔪_K`), `hintegral` and `hfinite` (integrality or finiteness of every extended valuation ring). Results using them are conditional.
- The Henselian hypothesis on `base` alone does not give uniqueness here: the unconditional results assume that `O_K` is `𝔪_K`-adically complete or precomplete.
- `HasUniqueValuationExtension` compares `target` with valuations whose value groups lie in one fixed universe.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteExtension/Core.lean`: the Lean file is the source byte for byte (SHA-256 `fb8861b1645b4573a35ad62a2b10c65c938d604cac59cd2266888af3df451a2b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
