# Continuous endomorphisms of Laurent series and power-series substitution

Module `FontaineWintenberger.Mathlib.Topology.LaurentSubstitution`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `k` be a field. The file shows that a continuous ring endomorphism of `LaurentSeries k` that fixes constants and sends the parameter `T` to a power series `g` without constant term acts on power series by the substitution `A ↦ A(g)`. Laurent series carry the topology of their `T`-adic valuation; power series carry the coefficientwise (product) topology `PowerSeries.WithPiTopology`.

## Results

Continuity statements, for `k` with a discrete uniform structure:

- `continuous_ofPowerSeries_valued`: the inclusion `HahnSeries.ofPowerSeries ℤ k : PowerSeries k → LaurentSeries k` is continuous from the coefficientwise topology to the valuation topology.
- `continuous_powerSeries_subst`: for `g` with `g.constantCoeff = 0`, the map `PowerSeries.subst g` is continuous for the coefficientwise topology.

The remaining theorems share these hypotheses: `F : LaurentSeries k →+* LaurentSeries k` is continuous, `F (HahnSeries.C a) = HahnSeries.C a` for all `a`, `g` is a power series with zero constant coefficient, and `F` sends `HahnSeries.single 1 1` (the parameter) to the image of `g`.

- `map_ofPowerSeries_eq_subst`: for every power series `A`, `F` sends the image of `A` to the image of `A.subst g`.
- `comp_apply_parameter`: if a second ring endomorphism `G` sends the parameter to the image of a power series `h`, then `F.comp G` sends the parameter to the image of `h.subst g`. Composition of maps thus reverses the order of the parameter series. No continuity or constant-fixing hypothesis is put on `G`.
- `iterate_ofPowerSeries_eq_subst_iterate`: the `n`-th iterate of `F` sends the image of `A` to the image of the `n`-th iterate of `PowerSeries.subst g` applied to `A`.
- `iterate_apply_parameter_eq_subst_iterate`: the same for `A = X`, the parameter.

## Proofs

For `continuous_ofPowerSeries_valued`, a neighbourhood of `0` in the valuation topology contains all series divisible by `T^N` for some `N`, and vanishing of the first `N` coefficients is an open condition in the coefficientwise topology. Substitution is identified with Mathlib's `PowerSeries.aeval`, which is continuous. For `map_ofPowerSeries_eq_subst`, the two maps `F ∘ j` and `j ∘ subst g` (with `j` the inclusion) are continuous and agree on polynomials, which are dense in `PowerSeries k`; inside the proof `k` is given the discrete uniformity.

## What to watch for

- The parameter image `g` is required to be a power series with zero constant coefficient; a unit condition on the leading coefficient is not asked.
- The statements concern only the restriction of `F` to (the image of) power series, not its values on all Laurent series.
- In the algebraic theorems `k` carries no topology in the statement; continuity of `F` refers to the valuation topology on `LaurentSeries k` alone.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/Topology/LaurentSubstitution.lean` (SHA-256 of the source file `46f01c02d31309004da02ef9cdbe2210f09457a4ada062c3e1273bbd85b53e17`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
