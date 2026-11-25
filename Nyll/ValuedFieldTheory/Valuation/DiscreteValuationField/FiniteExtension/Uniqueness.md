# Uniqueness of the extension of a complete discrete valuation

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite extension of fields with complete discrete valuations (`CompleteDVF`), the one on `L` extending the one on `K`. The file shows that for separable `L/K` every valuation of `L` extending that of `K` is equivalent to the given one, gives many reduction criteria, and derives consequences for the valuation ring `O_L`.

## Main definitions and results

- `HasUniqueValuationExtension base target`: every valuation `v'` of `L` extending the base valuation, with values in a linearly ordered commutative group with zero of a fixed universe, is equivalent (Mathlib's `Valuation.IsEquiv`) to the target valuation. `hasUniqueValuationExtension_toHenselianDVF` passes to the Henselian-DVF predicate.
- `hasUniqueValuationExtension_of_finite_separable`: the predicate holds when `L/K` is separable. Corollaries give equivalence and equality of valuation subrings for each extension `v'`, elementwise forms, the Henselian version, and `target_valuationSubring_eq_of_finite_separable` (every valuation subring whose valuation extends the base one is `O_L`).
- Assuming also the scalar tower `O_K → O_L → L`: `O_L` is the integral closure of `O_K` in `L`, module-finite and torsion-free over `O_K`; its maximal ideal is the only prime over that of `O_K`; and e·f = [L : K] (`ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_finite_separable`, `ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable`), so the extension is defectless (`isDefectless_of_finite_separable`).
- The valuation given by Chevalley's extension theorem can be chosen equivalent to the target valuation.
- `integralClosureEquivValuationSubring`: the `O_K`-algebra isomorphism from Mathlib's `integralClosure` to `O_L` when `O_L` is an integral closure.
- Criteria for uniqueness: equality of valuation subrings; module-finiteness of every extension ring; the valuative dichotomy of the integral closure with local, integral or finite inclusions, center equalities, or unique primes over the base maximal ideal; and, for separable `L/K`, integrality of every extension ring, the integral closure being local, a valuation ring, having one prime over the base maximal ideal, idempotent lifting in its fiber, or a Henselian condition on the extended maximal ideal.

## Proof

The integral closure `A` of `O_K` in `L` is Henselian along the extended maximal ideal (a result imported from another file); idempotent lifting leaves one prime in the fiber over the base maximal ideal, so `A` is local and, by Dedekind theory, a valuation ring. Every extension valuation ring contains `A` with center the maximal ideal of `A`, hence equals `A`.

## Caveats

- Uniqueness is up to equivalence and only over value groups in one universe `y`; the Chevalley corollaries and `target_valuationSubring_eq_of_finite_separable` take `y` to be the universe of `L`.
- Separability is assumed in the main theorem and its consequences.
- Most criteria take steps of the argument as hypotheses (the dichotomy `hval`, local inclusions, center equalities); they are reductions, discharged only along the separable route.
- `CompleteDVF` and the uniqueness predicate are the library's own notions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteExtension/Uniqueness.lean`: the Lean file is the source byte for byte (SHA-256 `1c130ea3777f65d3fcc02a2d7684dc1404442db3b5687ba40b97cee2ff12aa44`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
