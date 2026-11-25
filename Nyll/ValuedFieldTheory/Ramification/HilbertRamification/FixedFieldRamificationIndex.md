# The ramification index of L over a fixed field L^H

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FixedFieldRamificationIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of discretely valued fields in which the valuation of `K` extends uniquely to `L`, and `H` a subgroup of `Gal(L/K)` with fixed field `M = L^H`. The file defines `e(L/M)` from the inclusion of the restricted valuation ring `O_M = O_L ∩ M` into `O_L`, relates it to the normalized valuations, and shows that it equals the order of the zeroth group of the filtration that the library's depth function induces on `H`. The file's comment notes that no completeness or Henselian hypothesis is used.

## Main definitions and results

- `fixedFieldRamificationIndex H : ℕ`: the ramification index (`Ideal.ramificationIdx'`) of the maximal ideal of `O_M` in `O_L` along the inclusion.
- `map_fixedField_maximalIdeal_eq_pow_ramificationIndex` (`H` normal, unique extension `huniq`): `𝔪_M·O_L = 𝔪_L^e`.
- `fixedFieldRamificationIndex_ne_zero` (same hypotheses): `e ≠ 0`.
- `addVal_fixedFieldValuationSubringToTarget_eq_ramificationIndex_nsmul` (same hypotheses): for `a ∈ O_M`, the normalized additive valuation of `a` in `O_L` is `e` times its normalized additive valuation in `O_M`.
- `fixedFieldRamificationIndex_eq_card_depthLowerFiltration_zero` (`H` normal, `k_L/k_K` separable): `e(L/M)` equals the order of the zeroth group of `depthLowerFiltration H` for the ramification-number depth (`ramificationNumberDepthOfUniqueExtension`).

## Proofs

The ideal statements use that `O_M` and `O_L` are discrete valuation rings: the image of `𝔪_M` is a nonzero ideal of `O_L`, hence a power of `𝔪_L`. For the cardinality, private lemmas show that the zeroth depth subgroup is the inertia subgroup of `H` acting on `O_L`, and that `|stabilizer| = |inertia|·f` when the residue extension is separable. From this and the fundamental identity, `|inertia| = e` follows without assuming the residue field perfect. The last step uses that `H` is a Galois group of `O_L` over `O_M`, which is finite, torsion-free and integral.

## Points to watch

- The cardinality statement assumes the residue extension `k_L/k_K` separable; separability of `k_L` over the residue field of `M` is deduced from it.
- Uniqueness of the valuation extension is the explicit hypothesis `huniq`, and all four theorems assume `H` normal, although `e` is defined for any subgroup.
- The zeroth depth subgroup is the library's own construction from its depth function; the private lemma identifying it with inertia is not exported.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FixedFieldRamificationIndex.lean`: the Lean file is the source byte for byte (SHA-256 `fcd3e58d028099b1a98dd787fa2dfc03c355a8f68d46de167dd97fa0d6c3d8ee`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
