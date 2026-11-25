# The residue field of the field of norms, through a deep coordinate

Module `FontaineWintenberger.FieldOfNorms.Structure.Residue`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `L/K` be an infinite APF extension of a field `K` with `IsPerfectResidueLocalField K`, `D` a finite intermediate field and `𝔈 = deepFiniteTower K L D`. The file identifies the residue field of the valuation ring of `FieldOfNorms K L` with the residue field of the finite field `𝔈 0`, by reducing the coordinate at `𝔈 0`, and deduces that the residue field of the field of norms is perfect.

## Main definitions and results

- `FieldOfNorms.truncation_surjective`: each truncation map from the valuation ring to `DeepFiniteTowerQuotient K L D n` is surjective.
- `FieldOfNorms.residueReduction`: the ring homomorphism from the valuation ring to the residue field of `𝔈 0`, obtained from the truncation at stage `0` (a quotient by `𝔪²`) followed by the quotient map. By `residueReduction_apply` it is the residue of the integral coordinate at `𝔈 0`.
- `residueReduction_surjective`, `residueReduction_ker`: this map is surjective and its kernel is the maximal ideal of the valuation ring.
- `FieldOfNorms.residueToLayer`: the induced homomorphism on the residue field.
- `FieldOfNorms.residueLayerEquiv`: the resulting ring isomorphism between the residue field of the field of norms and the residue field of `𝔈 0`; `residueLayerEquiv_residue` gives its value on the residue of an integral family.
- `FieldOfNorms.instPerfectFieldResidueField` (an instance): the residue field of the field of norms is perfect.

## Proofs

Surjectivity of the truncations follows from surjectivity of the transition maps of the tower and from the equivalence `FieldOfNorms.truncationEquiv` between the valuation ring and the inverse limit. The kernel is computed with `FieldOfNorms.valuation_eq_deepFiniteTower`: the valuation of a norm family is the normalized valuation of its coordinate at `𝔈 0`. Perfectness is transported along `residueLayerEquiv` for `D = apfResidueLayer K L`, composed with `integralClosureResidueEquiv`, from the perfectness of the residue field of the integral closure of `𝒪[K]` in `L` (`IsAPF.perfectField_integralClosureResidue`).

## Points to watch

- The isomorphism here depends on the chosen tower, hence on `D`, and its target is the residue field of a finite stage, not that of `L`. The identification with the residue field of `L` is made elsewhere in the library.
- No finiteness of the residue field is assumed.
- Infinitude of `L/K` is the hypothesis `Fact (¬ Module.Finite K L)`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Structure/Residue.lean` (SHA-256 of the source file `9467d9b64c40b84d1ef2d7bbeff45bfc7f1f130d3f1fc85fc5402392d189ad5e`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
