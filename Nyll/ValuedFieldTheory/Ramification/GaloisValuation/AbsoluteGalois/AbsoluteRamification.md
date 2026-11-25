# Decomposition and inertia in the absolute Galois group

Module `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.AbsoluteRamification`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K`, `G_K = Gal(K̄/K)` with `K̄` the algebraic closure, and a valuation ring `A` of `K̄`, the file studies the decomposition subgroup `D_A` (the stabilizer of `A`) and the inertia subgroup `I_A` (the kernel of the action of `D_A` on the residue field `k_A`): conditions for `D_A = G_K`, and the exact sequence `I_A → D_A → Aut(k_A)`.

## Main definitions

- `decompositionSubgroup K A`, `inertiaSubgroup K A` (a subgroup of `D_A`), `inertiaSubgroupInAbsolute K A` (its image in `G_K`).
- `decompositionResidueAction K A : D_A →* Aut(k_A)`; `inertiaSubgroup_eq_ker` says `I_A` is its kernel, so `I_A` is normal in `D_A`.
- `absoluteResidueActionOfDecompositionSubgroupEqTop K A hA`: given `hA : D_A = G_K`, the residue action on all of `G_K`. `absoluteResidueActionOfHenselianDVF` is the same map with unused extra arguments: `F` and the instance that `A.valuation` extends `F.valuation`.
- `decompositionQuotientInertiaEquivResidueActionRange`: `D_A / I_A ≃*` the image of the residue action; `absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop`: the same for `G_K / I_A` when `D_A = G_K`.

## Main results

- `decompositionSubgroup_eq_top_of_finite_separable_restrictUnique`: if `A` extends a valuation `v` of `K` and, for every finite separable `E / K` in `K̄`, every valuation ring of `E` extending `v` equals `A ∩ E`, then `D_A = G_K`. Proof: some `z^n` with `n > 0` lies in such an `E`, where uniqueness gives invariance, and `z ∈ A` iff `z^n ∈ A`.
- Variants for `F` a Henselian discretely valued field (`HenselianDVF`): the same conclusion if every such valuation ring of every `E` is integral (`…_integral`) or finite (`…_moduleFinite`) over that of `F`, or if each level `E` carries a `HenselianDVF` structure with valuation ring `A ∩ E` and the unique-extension property over `F` (`…_henselianUnique`, `…_powerRoute`); also one-level versions.
- `decompositionSubgroup_pointwise_smul`: the decomposition subgroup of `σ • A` is `σ D_A σ⁻¹`.
- Exactness of `I_A → D_A → Aut(k_A)`, and, when `D_A = G_K`, of `I_A → G_K → Aut(k_A)` with `I_A` normal in `G_K`; criteria for `I_A` to be trivial, `D_A` or `G_K`.

## Watch for

- No result here proves `D_A = G_K` for a Henselian field outright. Each such statement assumes uniqueness (or integrality, or finiteness) of valuation rings at all finite separable levels, i.e. the content of the Henselian unique-extension theorem; a comment calls supplying it the remaining finite-level task. `absoluteResidueActionOfHenselianDVF` takes `D_A = G_K` as an argument; its docstring names a theorem `decompositionSubgroup_eq_top_of_henselianDVF` that is not in this file.
- `D_A / I_A` is identified with the image of the residue action, not with all of `Aut(k_A)` or a Galois group of the residue field; surjectivity is not proved.
- `G_K` is the automorphism group of the algebraic closure, not of a separable closure.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/AbsoluteRamification.lean`: the Lean file is the source byte for byte (SHA-256 `e61f8aac2342258ab56375117b81c4223f082e1cd51461c282df639460a7d049`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
