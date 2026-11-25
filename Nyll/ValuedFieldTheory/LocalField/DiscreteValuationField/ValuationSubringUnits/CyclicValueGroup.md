# Cyclic value groups, rank one, and normalized uniformizers

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file gathers order-theoretic facts about value groups and uniformizers needed when a valuation is replaced by one valued in its actual range: a cyclic value group is Archimedean, so a nontrivial valuation into it is rank one; and for `ℤᵐ⁰`-valued valuations, an element of value `exp (-1)` is a uniformizer.

## Definitions and results

- `WithZeroValuation.rankOne`: for a nontrivial valuation `v` on a ring with values in `ℤᵐ⁰`, a `RankOne` structure, via the embedding `ℤᵐ⁰ → ℝ≥0` sending `exp n` to `2 ^ n`.
- `isCyclic_mulArchimedean`: a cyclic linearly ordered commutative group is multiplicatively Archimedean.
- `units_isCyclic_mulArchimedean`: a linearly ordered commutative group with zero whose unit group is cyclic is multiplicatively Archimedean.
- `rankOneOfUnitsIsCyclic`: a nontrivial valuation into such a group admits a `RankOne` structure (Mathlib's equivalence between rank one and the Archimedean property, applied to the value group).
- `isUniformizer_of_valuation_eq_exp_neg_one`: for a rank-one discrete `ℤᵐ⁰`-valued valuation on a field, `v π = exp (-1)` makes `π` a uniformizer.
- `exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective`: a surjective `ℤᵐ⁰`-valued valuation has an element of value `exp (-1)` in its valuation ring.

## Watch for

- `rankOne` and `rankOneOfUnitsIsCyclic` are definitions, not instances; the second is chosen non-constructively. The base `2` in `rankOne` is an arbitrary normalization.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/CyclicValueGroup.lean`: the Lean file is the source byte for byte (SHA-256 `a1bfd8a362c97730911fb1bdde27245e65151bce801781eaf4bfb0864b23b981`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
