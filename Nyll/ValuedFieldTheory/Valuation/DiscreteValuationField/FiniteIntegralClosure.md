# The integral closure of a complete DVR in a finite separable extension

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `O_K` be the valuation ring of a complete discretely valued field `K` (a `CompleteDVF`) and `L/K` a finite separable extension. The file studies the integral closure `A` of `O_K` in `L` directly, without a valuation on `L` given in advance, and shows that `A` is a complete discrete valuation ring; from it it builds a complete discrete valuation on `L` extending that of `K`.

## Main results

All results below assume `L/K` finite and separable.

- `integralClosure_base_maximal_map_isAdicComplete_of_finite_separable` and `integralClosure_henselianRing_of_finite_separable`: `A` is complete, and Henselian, for the ideal `m_K A`.
- `integralClosure_base_maximal_fiber_subsingleton_of_finite_separable`: the fiber of `A` over the maximal ideal of `O_K` has at most one prime.
- `integralClosure_isLocalRing_of_finite_separable`: `A` is local; `CanonicalIntegralClosure.maximalIdeal` names its maximal ideal `m_A`.
- `integralClosure_isDiscreteValuationRing_of_finite_separable` and `integralClosure_valuationRing_of_finite_separable`: `A` is a DVR and a valuation ring; `CanonicalIntegralClosure.mem_or_inv_of_finite_separable` gives the dichotomy `z ∈ A` or `z⁻¹ ∈ A` for `z : L`.
- `m_K A` is nonzero (finiteness is not used for this), contained in `m_A`, and equals `m_A ^ n` for some `n > 0`; `A` is `m_A`-adically complete.
- `exists_integralClosure_standard_completeDVF`: a `CompleteDVF` structure on `L`, with value group in universe 0 (the proof takes `ℤₘ₀`), whose valuation ring has exactly the elements of `A`. `exists_integralClosure_standard_fundamental_identity` adds that its valuation extends that of `K`, its ring is an integral closure of `O_K`, and degree = ramification index × residue degree.
- `exists_integralClosure_valuationSubring_of_finite_separable`: a valuation subring of `L` with underlying subring `A` whose valuation extends that of `K`.

Two helper lemmas, valid without finiteness or separability, show that `O_K → A` is injective and `A` is a faithful `O_K`-module.

## Proof

`A` is module-finite over the noetherian, integrally closed `O_K`, so it inherits adic completeness and is Henselian along `m_K A`. The fiber over `m_K` is Artinian; idempotents lift to `A`, a domain, so they are 0 or 1, and the fiber has one prime. Lying-over then leaves one maximal ideal. A local Dedekind domain that is not a field is a DVR.

## Caveats

- Separability is assumed in every result except the two helper lemmas.
- `exists_integralClosure_standard_rankOneDiscrete_valuation` and `exists_integralClosure_standard_complete_valuation_data` assert only the existence of some ring isomorphism between `A` and the valuation ring, not one compatible with the inclusions into `L`.
- Degree, ramification index and residue degree are the library's `ValuedExtension` invariants.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`: the Lean file is the source byte for byte (SHA-256 `cfcddf5c084584e138bb06120ecc6aacbfea391de492eb007fb70b92c2e2ec99`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
