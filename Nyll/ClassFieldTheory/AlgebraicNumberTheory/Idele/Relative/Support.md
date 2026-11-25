# Coefficient support of relative ideles

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.Support`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L/K` of number fields, the relative adele ring `RelativeAdeleRing K L` is `𝔸_K ⊗[K] L`. Fixing a `K`-basis of `L`, every relative adele has finitely many coefficients in `𝔸_K`. This file uses these coefficients to attach to a relative idele a finite set of finite places of `K` outside which its local components, and those of its inverse, lie in the lattice spanned by the basis over the valuation ring of `K_w`.

## Main definitions and results

- `relativeExtensionBasis`, `relativeAdeleBasis`, `relativeAdeleCoefficient`: the chosen basis of `L` over `K` (`Module.Free.chooseBasis`), its extension to an `𝔸_K`-basis of `𝔸_K ⊗[K] L`, and the `i`-th coefficient of a relative adele. `relativeAdele_eq_sum_tmul_coefficients` writes `z = Σ cᵢ ⊗ bᵢ`; the finite and infinite components are computed coefficientwise.
- `adeleNonIntegralPlaces a`: the finite set of finite places where an adele of `K` is not integral, with its membership lemma.
- `relativeAdeleCoefficientSupport z` and `relativeIdeleCoefficientSupport z`: the union of the non-integral places of all coefficients, for a relative adele, and for a relative idele together with its inverse.
- `relativeIdele_coefficients_integral_of_notMem`: outside this support all coefficients of `z` and `z⁻¹` are integral at `w`; `relativeIdeleCoefficientSupport_minimal`: the support is contained in every finite set with this property.
- `RelativeBasisIntegralAt w x`: `x ∈ K_w ⊗[K] L` is a combination of the basis vectors with coefficients in the valuation ring of `K_w`. `RelativeBasisIntegralUnitAt w x`: this holds for a unit `x` and for `x⁻¹`.
- `relativeIdele_finiteComponent_basisIntegralUnit_of_notMem`: outside the support, the finite component of a relative idele is a basis-integral unit. `exists_relativeIdele_coefficientSupport` packages the coefficient and local statements in one existence statement.

## Proof

Each coefficient is an adele of `K`, hence integral at almost all places by the restricted-product condition of Mathlib's adele ring; the local component at `w` is the sum of the `w`-components of the coefficients tensored with the basis vectors.

## Points to watch

- Everything built from the coefficients depends on the basis chosen by `Module.Free.chooseBasis`; the support sets are not canonical. `adeleNonIntegralPlaces a`, for an adele `a` of `K`, does not involve the basis.
- `RelativeBasisIntegralAt` is integrality in the lattice spanned by this basis, not integrality in the product of the valuation rings of the completions of `L` above `w`. The module comment says that passing to the latter needs an extra integral compatibility of the local tensor decomposition, which this file does not provide.
- Only finite places enter the support; nothing is said at infinite places beyond the coefficientwise formula.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Relative/Support.lean`: the Lean file is the source byte for byte (SHA-256 `d5a021739e86696848110a04b6b2ea45e08693293827ddad57704d8c0428c62f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
