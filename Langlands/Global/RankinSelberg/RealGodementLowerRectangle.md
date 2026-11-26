# Lower rectangle insertion in the real Godement coefficient

This module is the real counterpart of the Library's `ComplexGodementLowerRectangle`. Let `t < r`
and let `X` be an `(r+1-(t+1)) × (t+1)` real matrix.

* `lowerRectangle h X ∈ GL_{r+1}(ℝ)` is the lower unipotent block matrix `[[1, 0], [X, 1]]`, with
  blocks of sizes `t + 1` and `r + 1 - (t + 1)`. `determinant_lowerRectangle`: its determinant is one.
* `rectangularPoint_eq_pad_lowerRectangle`: the argument
  `ArchimedeanLocal.rectangularPoint g X = diag([[g, 0], [X, 1]], 1)` of the dual unequal-rank
  integral equals `diag(diag(g, 1) · lowerRectangle h X, 1)`.

`RealGodementLowerRectangleStatement` (proved by `realGodementLowerRectangle`): with `ν`, `μ₁`,
`μ₂`, `κ` and `D` as in `RealGodementTwoBlockRestrictionStatement` for `k = t + 1`, there is
`C > 0` such that for every test `Φ` separated by `F` and `f`, every
`U ∈ realUniformWhittakerModel r ds (-a)`, `g ∈ GL_{t+1}(ℝ)` and `X`, the two-block kernel
`twoBlockRestrictionKernel … g (lowerRectangle h X)` is integrable for `rightTailProductMeasure` and

`realAdjacentGodementCoefficient D a Φ U c (rectangularPoint g X) =
realAdjacentWeylSign r c · P g (1/2) · C · ∫ twoBlockRestrictionKernel … g (lowerRectangle h X) p dp`.

The proof is the two-block formula of `RealGodementTwoBlockRestriction` with
`b = lowerRectangle h X`; the character and determinant power of `b` equal one because its
determinant is one. This is the pointwise identity used before integrating over the lower rectangle
in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §§9.1 and 10.1.
