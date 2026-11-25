# The relative field of norms is a separable closure

Module `FontaineWintenberger.FieldOfNorms.Relative.SeparablyClosed`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `L/K` an infinite separable APF extension, and `Ω` a separable closure of `K` containing `L`. The file proves that the relative field of norms `RelFieldOfNorms K L Ω`, the direct limit of the norm fields of the finite extensions of `L` in `Ω`, is separably closed, and hence is a separable closure of the norm field `FieldOfNorms K L`.

## Main results

* `FieldOfNorms.fieldValuation_hasExtension_inclusion`: for `M/L` finite, the valuation of `FieldOfNorms K M` extends that of `FieldOfNorms K L` along `FieldOfNorms.inclusion` (`Valuation.HasExtension`).
* `exists_finite_fieldOfNorms_exact_root`: a monic polynomial `f` of positive degree over the valuation ring of `FieldOfNorms K L`, separable over the field, has a root in `FieldOfNorms K N` for some finite extension `N` of `L` in `Ω` with `[N:L] ≤ deg f`.
* `exists_finite_fieldOfNorms_root_of_monic`: the same for any monic separable polynomial of positive degree over `FieldOfNorms K L`.
* `RelFieldOfNorms.exists_root_of_monic`: every monic separable polynomial of positive degree over `RelFieldOfNorms K L Ω` has a root there.
* `RelFieldOfNorms.isSepClosed`: `RelFieldOfNorms K L Ω` is separably closed.
* `RelFieldOfNorms.isSepClosure`: it is a separable closure of `FieldOfNorms K L` (`IsSepClosure`).

General lemmas on polynomials over a field `F`:

* `separable_scaleRoots_of_monic`: `f.scaleRoots s` is separable when `f` is monic separable and `s ≠ 0`.
* `exists_integral_scaleRoots_of_uniformizer`: for a valuation `v` with values in `WithZero (Multiplicative ℤ)` and `π` with `v π = exp(-1)`, some positive power `s = π^m` makes all coefficients of `f.scaleRoots s` integral, `f` monic.
* `aeval_div_eq_zero_of_scaleRoots`: a root `a` of `f.scaleRoots s` gives the root `a / s` of `f`.

## Proofs

For the integral case, let `d` bound the valuation of the discriminant of `f`. `exists_fieldOfNorms_approximate_root_at_precision`, from `FontaineWintenberger.FieldOfNorms.Relative.ApproximateRoots`, gives a finite `N` and an integral `z` in `FieldOfNorms K N` with `f(z)` of valuation at most `exp(-(2 · deg f · d + 1))`. The norm-field inclusion raises valuations to a power `e ≤ [N:L] ≤ deg f`, so `f(z)` is smaller than the square of the discriminant, and the Newton–Krasner root extraction `discreteValued_exists_root_mem_adjoin_of_discr` produces an exact root. A general monic polynomial is reduced to the integral case by scaling roots with a power of `FieldOfNorms.uniformizer K L`. A polynomial over the limit descends to a stage `N` (`RelFieldOfNorms.exists_polynomial`); the previous result is applied with `N` as base field. Separable closedness follows from Mathlib's criterion `IsSepClosed.of_exists_root`.

## Remarks

`Ω` is assumed to be a separable closure of `K` (`IsSepClosure K Ω`) with a compatible `L`-algebra structure; separability of `Ω/L` is derived inside the statements.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Relative/SeparablyClosed.lean` (SHA-256 of the source file `7b3f2da91461429a2d3d0372efc881c51cf825d4f340168afe2d6e75bf58bb65`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
