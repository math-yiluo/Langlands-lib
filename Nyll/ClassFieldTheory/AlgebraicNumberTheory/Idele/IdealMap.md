# The fractional ideal of an idele

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, the file constructs the map from ideles to nonzero fractional ideals, `a ↦ ∏_v 𝔭_v ^ ord_v(a_v)`. It proves that the map is surjective, that its kernel consists of the ideles that are units at every finite place, and that the composite to the ideal class group is surjective. The map is built in two steps: the vector of local orders, then unique factorization of fractional ideals.

## Local orders and valuation vectors

- `FiniteIdeleGroup.localOrder v : K_vˣ →* Multiplicative ℤ`, with `ord_v(x) = −log v(x)` for Mathlib's `ℤᵐ⁰`-valuation, so a uniformizer has order 1 (`localOrder_apply`). The order is 0 exactly on the local units (`localOrder_eq_zero_iff`).
- `finite_nonLocalUnits`, `valuationVectorAdd`, `valuationVector`: a finite idele is a non-unit at finitely many places, so its orders form a finitely supported vector `HeightOneSpectrum (𝓞 K) →₀ ℤ`; this is a homomorphism.
- `chosenLocalOrderSection v n` and `valuationVectorSection e`: chosen local elements and finite ideles with prescribed orders, which give `valuationVector_surjective`.

## Fractional ideals

- `FractionalIdealGroup K`: the unit group of fractional ideals of `𝓞 K`. `prime v` is the prime of `v`, `primePowerHom` its powers, and `factorization` sends an exponent vector to `∏ 𝔭_v ^ n_v`.
- `count_factorization`, `ext_count`, `factorization_injective`, `factorization_surjective`, `factorizationEquiv`: exponent vectors and nonzero fractional ideals correspond one to one, by Mathlib's factorization of fractional ideals.

## The ideal map

- `FiniteIdeleGroup.fractionalIdeal` and `IdeleGroup.fractionalIdeal`, surjective; the archimedean components do not contribute.
- `integralSubgroup` and `integralAtFinitePlaces`: the ideles that are units at every finite place. `fractionalIdeal_ker` identifies them as the kernel, and `quotientIntegralEquiv` gives `IdeleGroup K ⧸ integralAtFinitePlaces ≃* FractionalIdealGroup K`.
- `IdeleGroup.idealClass : IdeleGroup K →* ClassGroup (𝓞 K)`, surjective (`idealClass_surjective`), and `quotientIdealClassKernelEquiv`, the quotient by its kernel.

## Points to watch

- The docstring of `quotientIdealClassKernelEquiv` refers to an identification of the kernel with the product of `integralAtFinitePlaces` and `Kˣ`; that identification is not made in this file.
- Most local constructions are specializations of generic results on restricted products of discretely valued fields, in `RestrictedProduct.DiscreteValuation`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/IdealMap.lean`: the Lean file is the source byte for byte (SHA-256 `808d2f421b6d3c5fe9ecb8cca4e2a0f550d4f8612442c5ffeddd033fc1d0105a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
