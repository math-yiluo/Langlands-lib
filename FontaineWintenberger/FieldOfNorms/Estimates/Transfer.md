# Ramification transfer to the field of norms

Module `FontaineWintenberger.FieldOfNorms.Estimates.Transfer`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, with residue characteristic `p`, and let `L/K` be an infinite separable APF extension. A `K`-automorphism `σ` of `L` acts on the field of norms `FieldOfNorms K L`. The file defines a ramification number for this action and proves that it equals the ramification number of the restriction of `σ` to every sufficiently large finite intermediate field, including fields that `σ` does not preserve.

## Definitions

- `FieldOfNorms.integerAut`: the automorphism of the valuation ring of the field of norms induced by `σ`; `FieldOfNorms.residueAut`: the induced automorphism of its residue field.
- `FieldOfNorms.ramificationNumber`: the element of `EReal` equal to `ramificationOrder` of `integerAut σ` minus one.
- `algebraicResidueAut`: the action of `σ` on the residue field of the integral closure of `𝒪[K]` in `L`.
- `FiniteIntermediateField.autPairField`, `autPairLeft`, `autPairRight`: for a finite intermediate field `E`, the compositum of `E` and `σ(E)`, with the inclusion of `E` and the embedding `x ↦ σ(x)`.
- `FiniteIntermediateField.ramificationNumber`: `embeddingRamificationNumber` of this pair of embeddings.

## Results

- `FieldOfNorms.ramificationNumber_eq_top_iff`: the number is `⊤` exactly when `σ = 1`; otherwise it is `n − 1` for a natural number `n`.
- `FieldOfNorms.ramificationNumber_eq_uniformizer`: when `residueAut σ` is trivial, the number is the valuation of `σ(π) − π` minus one for any uniformizer `π`.
- `FieldOfNorms.mapEquiv_residueConstants`, `residueAut_eq_refl_iff_algebraicResidueAut`: the residue constants are equivariant, so `residueAut σ` is trivial exactly when `algebraicResidueAut σ` is.
- `FiniteIntermediateField.ramificationNumber_eq_top_iff`, `ramificationNumber_eq_aut`: the finite number is `⊤` exactly when `σ` fixes `E` pointwise; on a `σ`-stable `E` it is the number of the restriction.
- `FiniteIntermediateField.ramificationNumber_eq_of_lt_relativeFirstBound`: for `apfMaximalTame K L ≤ E ≤ F`, with `σ` not fixing `E`, if the number at `E` is less than `apfRamificationBound E F`, the numbers at `F` and `E` agree.
- `exists_finiteIntermediateField_ramificationNumber_eq`: there is a finite intermediate field `E` such that, for every finite `F ⊇ E`, `FiniteIntermediateField.ramificationNumber σ F = FieldOfNorms.ramificationNumber σ`.

## Proof

If `σ` acts non-trivially on residues, both numbers are `−1` above `apfMaximalTame K L`. Otherwise the number on the field of norms is computed on its uniformizer; `FieldOfNorms.valuation_sub_eventually_coordinate` shows that the valuation of `σ(π) − π` is that of its coordinates at deep layers, which gives equality on stable layers. A stable normal closure `E` is then chosen so deep that the relative ramification bounds above it exceed the number (`IsAPF.exists_finiteIntermediateField_relativeFirstBound_ge`). Non-stable layers are handled inside a finite Galois extension (`exists_finiteGalois_embedding_restrictions`).

## To watch for

- The numbers are "signed": the library's own `ramificationOrder` (or `embeddingRamificationNumber`) minus one, in `EReal`, with `−1` for non-inertial automorphisms.
- `L/K` is not assumed normal.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/Transfer.lean` (SHA-256 of the source file `64ee20bd2a09fcfad34b89ba6d1d169851e81fd420276dd05bb54a41b12a9ea6`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
