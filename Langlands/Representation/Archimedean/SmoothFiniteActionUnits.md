# Genuine derivative operators on finite vectors of a restricted units action

This is an internal consequence of the covariance and basis-expansion lemmas in [SmoothUnitAction](SmoothUnitAction.md), on the actual orbit-span carriers of [FiniteVectors](../FiniteVectors.md).

Let `A` be a finite-dimensional complete real normed algebra and `R` a representation of `Aˣ` by bounded complex-linear operators on a complex normed space. Let `D` be its genuine smooth carrier, let `j : K →* Aˣ` be a monoid homomorphism, and let `ρ` be the restriction of the transported group action to `K` through `j`. For each `X : A`, `isFiniteVector_operator_units` proves that `dR(X)` preserves the vectors of `D` with finite-dimensional complex `ρ`-orbit span. No topology or compactness of `K` is needed.

For such a vector `v`, write `W` for its orbit span and fix a finite real basis `b` of `A`. For `g = j(k)`, covariance at `g⁻¹` gives

`ρ(k) dR(X)v = dR(gXg⁻¹) ρ(k)v`.

Expanding the direction `gXg⁻¹` in `b` puts this translate in the finite sum of the images `dR(bᵢ)(W)`. That sum is finite-dimensional over `ℂ`, so the orbit span of `dR(X)v` is finite-dimensional. `finiteVectorsOperator` restricts the actual complex-linear endomorphism `dR(X)` to the finite-vector submodule, and `coe_finiteVectorsOperator` identifies its value under inclusion.

With the maximal compact group of real or complex `GL_n` and `j = Unitary.toUnits`, the restriction is the derivative operator on the genuine compact-finite smooth submodule. This file does not assert a complexified Lie bracket law, admissibility, or algebraic irreducibility.
