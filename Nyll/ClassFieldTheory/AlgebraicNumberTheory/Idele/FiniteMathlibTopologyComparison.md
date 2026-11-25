# Ideles and adele units as topological groups

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FiniteMathlibTopologyComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, the library's `IdeleGroup K` is the archimedean units times a restricted product of the `K_vˣ` over the local unit groups. Mathlib uses the units of the adele ring instead. The file shows that the algebraic isomorphism between the two is a homeomorphism.

## Main declarations

- `finiteEquivFiniteAdeleUnitsContinuousMulEquiv`: `FiniteIdeleGroup K ≃ₜ* (FiniteAdeleRing (𝓞 K) K)ˣ`, from the library's `RestrictedProduct.unitsContinuousMulEquiv`, since the local valuation rings are open. By `finiteEquivFiniteAdeleUnitsContinuousMulEquiv_apply`, it agrees with the algebraic map `finiteEquivFiniteAdeleUnits`.
- `continuous_finiteEquivFiniteAdeleUnits`, `continuous_equivAdeleRingUnits`: the algebraic comparisons are continuous, because `u` and `u⁻¹` are restricted products of continuous local maps.
- `equivAdeleRingUnitsContinuousMulEquiv`: `IdeleGroup K ≃ₜ* (AdeleRing (𝓞 K) K)ˣ`.

## Points to watch

- Adele units carry Mathlib's topology on a group of units, induced by `u ↦ (u, u⁻¹)`, not the subspace topology.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/FiniteMathlibTopologyComparison.lean`: the Lean file is the source byte for byte (SHA-256 `2b5cbd7e2b53447d86ba663eccf0dda01ec2ff55d0c173b94ff6e9082568a6f9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
