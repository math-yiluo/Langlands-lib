# A standard Lubin–Tate level is unchanged by a deep unit change

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.HigherUnitLevelEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with residue field of cardinality `q`, `π` a uniformizer, and `u` a unit with `u ∈ U^(n+1)`. Put `d = (q − 1)·q^n`. The file proves that the standard Lubin–Tate level `n` for `uπ` is isomorphic over `K` to the level `n` for `π`, and concludes that `u` is a norm from the latter level. The argument is a Krasner-type root comparison and does not depend on the characteristic.

## Main results

- `standardLubinTatePrimitivePolynomial_map_levelCoefficientHom_splits`: the primitive polynomial of level `n` splits over the valuation ring of its own level; its `d` roots come from the finite unit parameters.
- `standardLubinTatePrimitivePolynomial_derivative_eval₂_addVal`: the derivative of the primitive polynomial at the primitive point has additive valuation `n·d + (q − 2)·q^n`, which equals `(n + 1)·d − q^n` (`standardLubinTatePrimitivePolynomial_derivativeExponent_eq`); every root has the same derivative valuation.
- In the common compositum of the two levels (built in another file): the changed polynomial is monic and splits; its value at the original primitive point `α` has valuation at least `e·d·(n + 2)`, `e` the ramification index of the original level in the compositum; its derivative at each root has valuation `e'·(n·d + (q − 2)·q^n)`, where `e'`, the ramification index of the changed level, equals `e`.
- `exists_standardLubinTateChangedPrimitiveRootInCompositum_close`: there is a root `β` of the changed polynomial with `v(α − β) > e·q^n`.
- `standardLubinTateHigherUnit_restrict_changedLevel_eq_originalLevel`: inside the compositum, the two levels are the same intermediate field.
- `standardLubinTateHigherUnitChangedLevelAlgEquiv`: the resulting `K`-algebra isomorphism from the changed level to the original level.
- `standardLubinTateUnitFactorFieldUnit_mem_standardNormSubgroup_of_mem_higher`: `u` lies in the norm subgroup of the original level `n`.

## Proof

The derivative valuation comes from the chain rule along the iterates of `X^q + πX`, each factor `q·y^(q−1) + π` having the valuation of `π`. A root-proximity lemma for split monic polynomials gives a root `β` with `v(α − β) ≥ e·q^(n+1)` from the two estimates. Every nontrivial Galois displacement of `α` has valuation at most `e·q^n` (from the displacement bound at level `n`), so any automorphism fixing `β` fixes `α`. Thus `K(α) ⊆ K(β)`, the original level lies in the changed one, and equal degrees `d` give equality. The norm statement then follows from the transport lemma in the file on changed uniformizers.

## Points to watch

- The hypothesis `u ∈ U^(n+1)` is essential; for an arbitrary unit the two levels are not compared here.
- The isomorphism is constructed through the chosen common compositum, not as an explicit map on division points.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `429bdf2cf0950e4dc65d2461dffde1074b8abd5cf8ed74c5777abdbaca252907`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
