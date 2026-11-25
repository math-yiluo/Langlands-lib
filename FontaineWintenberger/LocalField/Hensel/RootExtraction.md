# Exact roots from approximate roots, with the discriminant as radius

Module `FontaineWintenberger.LocalField.Hensel.RootExtraction`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete ultrametric normed field and `f` a monic polynomial of positive degree over its valuation ring `𝒪[K]`, with discriminant `disc f`. The file shows that an integral element `z` with `‖f(z)‖ < ‖disc f‖²` lies within distance `‖disc f‖` of a unique root of `f`, and that for `z` in a finite separable extension this root lies in `K(z)`.

## Main results

- `unitBall_root_eq_of_norm_sub_lt_discr`: two roots of `f` in `𝒪[K]` that are both at distance `< ‖disc f‖` from a point `z` are equal (no completeness needed).
- `unitBall_hensel_of_discr`: if `z ∈ 𝒪[K]` and `‖f(z)‖ < ‖disc f‖²`, there is a root `a ∈ 𝒪[K]` with `‖a − z‖ < ‖disc f‖`, unique with this property.
- `exists_root_near_of_discr`: the same for `z` of norm `≤ 1` in a finite-dimensional normed extension field `L` of `K`, with uniqueness among all roots in `L`.
- `exists_root_mem_adjoin_of_discr`: if moreover `L/K` is separable, the root lies in `K⟮z⟯`.
- `discreteValued_exists_root_mem_adjoin_of_discr`: the same statement for a complete field `K` with a rank-one discrete valuation `v` whose valuation ring is a discrete valuation ring, a finite separable extension `L`, and a valuation `w` of `L` extending `v` (`v.HasExtension w`); norms are replaced by `w`, and `disc f` is read in `L`.
- `discreteValued_exists_root_mem_adjoin_of_discr_additive`: the additive form: `2 · w(disc f) < w(f(z))` gives the unique root `a` with `w(disc f) < w(a − z)`.

## Proofs

Lemmas of the library's discriminant file give `‖disc f‖ ≤ ‖f′(z)‖` when `‖f(z)‖ < ‖disc f‖` (`valuation_discr_le_derivative`) and `‖disc f‖ ≤ ‖a − b‖²` for distinct roots (`valuation_discr_le_sub_sq`). The first yields the hypothesis of `unitBall_hensel_nonunit`; the second gives separation of roots. For the finite extension, `f` is mapped to `𝒪[L]`, and `L` is complete. Membership in `K⟮z⟯` is obtained by embedding `L` in a separable closure with its spectral norm and applying Krasner's lemma (`krasner_mem_adjoin`), the conjugates of the root being separated by the discriminant. The valuation versions equip `K` with `discreteValuedNormedField` and `L` with the spectral norm, whose unit ball is the valuation ring of `w`.

## Points to watch

- `f` must be monic of positive degree with coefficients in the valuation ring of the base field, and `z` must be integral.
- The radius is the discriminant, not the derivative at `z`; the hypothesis `‖f(z)‖ < ‖disc f‖²` forces `disc f ≠ 0`.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Hensel/RootExtraction.lean` (SHA-256 of the source file `3c081b1dfa25606d577e1a62052b8d22e15aa0919adbc4d2e53cccc1567356d9`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
