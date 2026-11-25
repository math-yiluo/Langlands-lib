# Structure of the first principal units in mixed characteristic

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a complete discretely valued field `K` of characteristic zero with finite residue field of characteristic `p`, the file proves that the first principal units `U^1` are, as a topological group, `ℤ/p^a × ℤ_p^d` for some `a`, where `d = [K : ℚ_p]`. This is the principal-unit factor of the mixed-characteristic structure theorem for the units of a local field.

## Algebra over a PID

- `finite_rank_and_torsion_projection_of_surjective`: for `R` a principal ideal domain and a surjection `f : M → Q` onto a finite torsion module whose kernel is finite free of rank `d`, the module `M` is finitely generated of rank `d`, its torsion is finite and injects into `Q`, and `M` modulo torsion has rank `d`. The output is the structure `FiniteRankTorsionProjectionData`; `finite_rank_torsion_data_of_setup` takes the map and its hypotheses bundled as a `FiniteQuotientSetup` (with `Q` finite) and returns a `FiniteRankTorsionData`.
- `isAddCyclic_of_injective_multiplicative_map`: a finite group embedding into the units of a domain is cyclic; `exists_card_eq_prime_power_of_injective_addMonoidHom`: a finite group embedding into a `p`-group has `p`-power order.

## Principal units

The setting is a valuation `v : K → ℤᵐ⁰`, complete and discrete, surjective, with finite residue field, `[CharZero K]`, and `F = ofWithZeroValuation v`; `e` is the ramification index.
- `mixed_principalUnitSuccKernelData`: if `e/(p − 1) < n`, then `U^(n+1)`, as a `ℤ_p`-submodule of `U^1`, is finite free of rank `d`.
- `mixed_firstPrincipalUnitFiniteQuotientSetup`: the projection `U^1 → U^1/U^(n+1)`, a surjection onto a finite torsion module with that kernel.
- `chosenMixed_firstPrincipalUnitAlgebraicData`: `U^1` is a finitely generated `ℤ_p`-module whose torsion is cyclic of order `p^a` and whose torsion-free quotient has rank `d`.
- `mixed_firstPrincipalUnitStructure`: a pair of `a` and an isomorphism of topological groups `ℤ/p^a × ℤ_p^d ≃ₜ* U^1` (the left side written multiplicatively); `chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation` chooses `n` itself.

The rank comes from the deep principal units (imported); torsion is cyclic because it lies in `Kˣ`, and a `p`-group because it injects into the finite quotient, which is a `p`-group (`discretePrincipalUnitQuotient_isPGroup`). Compactness follows from finite generation over `ℤ_p`.

## Points to watch

- The two structure results are `def`s giving data (a `Σ`-type), not propositions. The exponent `a` and the isomorphism are chosen and not identified further (for instance with roots of unity).
- The field must come from a normalized `ℤᵐ⁰`-valued valuation through `ofWithZeroValuation`, giving a `LocalField.{u, 0}`; the topology is `Valued.mk' v` and the `ℤ_p`-module structure on `U^1` is the library's own, all introduced locally by `let`.
- `d` is the rank over `ℚ_p` for the algebra structure of the library's `MixedQPadicContext`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/MixedCharacteristicStructure/Core.lean`: the Lean file is the source byte for byte (SHA-256 `329b524f95e42c86b35e1f1674bd1e9bac78296067103a01427a3d887070a0b2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
