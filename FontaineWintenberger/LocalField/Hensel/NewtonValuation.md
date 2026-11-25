# Newton–Hensel lifting for a discretely valued field

Module `FontaineWintenberger.LocalField.Hensel.NewtonValuation`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a field with a `Valued K Γ` structure whose valuation `v` is rank-one discrete (`Valuation.IsRankOneDiscrete`), complete for the valuation uniformity. The file restates the Newton–Hensel lemma with a non-unit derivative in terms of `v` and its valuation ring `𝒪`, with no norm in the statement.

## Main results

- `discreteValued_hensel_nonunit`: let `f` be a polynomial over `𝒪` and `z ∈ 𝒪` with `v(f(z)) < v(f′(z))²`. Then there is `a ∈ 𝒪` with `f(a) = 0`, `v(a − z) < v(f′(z))`, `v(f′(a)) = v(f′(z))`, `v(a − z) = v(f(z)) / v(f′(z))`, and every root `b ∈ 𝒪` with `v(b − z) < v(f′(z))` equals `a`.
- `discreteValued_hensel_nonunit_additive`: the same statement for the additive valuation `Valuation.toAddValuation v`: the hypothesis reads `2 · w(f′(z)) < w(f(z))`, and the root satisfies `w(a − z) = w(f(z)) − w(f′(z))`.
- `discreteValued_hensel_nonunit_ambient`: the same conclusions with the root regarded in `K`, and uniqueness among all `b ∈ K` with `f(b) = 0` and `v(b − z) < v(f′(z))`.
- `discreteValued_hensel_nonunit_ambient_additive`: the additive form of the previous statement.

## Proofs

`K` is given the norm `discreteValuedNormedField K Γ`, which is compatible with `v`: its unit ball is the valuation ring (`discreteValued_valuationSubring`) and it orders elements as `v` does (`discreteValued_norm_le_iff`). The normed statement `unitBall_hensel_nonunit` is then translated. For the ambient version, a root close to `z` is shown to be integral by the ultrametric inequality. The additive versions are restatements, since the additive valuation is the multiplicative one read in the order dual.

## Points to watch

- `v` is multiplicative, so closeness is expressed by small values; the additive statements reverse the inequalities.
- The derivative need not be a unit, and no assumption is made on the residue field.
- The value group `Γ` is any linearly ordered commutative group with zero; discreteness is the class `Valuation.IsRankOneDiscrete`.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Hensel/NewtonValuation.lean` (SHA-256 of the source file `f69c63596648ded96fba2bbf0b3074119603ed4049b335ea9ff588f9a6ea261d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
