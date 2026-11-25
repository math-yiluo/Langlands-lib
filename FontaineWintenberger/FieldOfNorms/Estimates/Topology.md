# Continuity of finite norms and the topology of ideal powers

Module `FontaineWintenberger.FieldOfNorms.Estimates.Topology`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file collects topological facts used for the field of norms: the field norm of a finite extension of complete normed fields is continuous, and in a discretely valued normed field the powers of the maximal ideal of the unit ball are closed balls, hence closed, complete, and a basis of neighbourhoods of zero.

## Continuity of norms

- `continuous_algebraNorm_of_finiteDimensional`: let `K` be a complete nontrivially normed field, and `E`, `F` normed fields that are normed `K`-algebras with `F` an `E`-algebra in a scalar tower and `F` finite-dimensional over `K`. Then `Algebra.norm E : F → E` is continuous.
- `FiniteIntermediateField.continuous_norm`: for finite intermediate fields `E ≤ F` of a separable extension `L/K`, with `K` complete and ultrametric, the norm `F → E` is continuous for the spectral norms.

The first is proved by writing the norm as the determinant of the matrix of left multiplication in a basis; that matrix depends `K`-linearly on the element, and a linear map out of a finite-dimensional space over a complete field is continuous.

## Ideal powers

Here `E` is a nontrivially normed ultrametric field whose unit ball `𝒪[E]` is a discrete valuation ring, and `π` an irreducible element of `𝒪[E]`.

- `norm_uniformizer_pos_lt_one`: `0 < ‖π‖ < 1`.
- `mem_maximalIdeal_pow_iff_norm_le`: `x` lies in the `n`-th power of the maximal ideal exactly when `‖x‖ ≤ ‖π‖ ^ n`; `n = 0` is included.
- `image_maximalIdeal_pow_eq_closedBall`: the image in `E` of the `n`-th power of the maximal ideal is the closed ball of radius `‖π‖ ^ n` about `0`.
- `isClosed_image_maximalIdeal_pow`: this image is closed.
- `nhds_zero_hasBasis_maximalIdeal_pow`: these images, for `n` in `ℕ`, form a basis of neighbourhoods of `0` in `E`.
- `isComplete_image_maximalIdeal_pow`: if `E` is complete, each image is complete. Nothing is assumed about the residue field.

## Spectral versions

For a complete discretely valued field `K`, a separable extension `L/K` and a finite intermediate field `E`, with its spectral norm:

- `FiniteIntermediateField.isClosed_image_maximalIdeal_pow`: the image in `E` of each power of the maximal ideal of `spectralIntegerRing K E` is closed.
- `FiniteIntermediateField.nhds_zero_hasBasis_maximalIdeal_pow`: these images form a basis of neighbourhoods of `0`.

## To watch for

The statements about finite intermediate fields install the spectral norm inside the statement (`spectralNorm.nontriviallyNormedField`), so the topology meant is the one of that norm.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/Topology.lean` (SHA-256 of the source file `2b6e97d825c75da740904efcbc3204ffdb8026cfbd1dde69ab292274c4e41749`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
