# The product map and the conjugation chart

The module `Langlands.Analysis.Local.WeylChartMaps` defines the two coordinate maps used near
a unit `γ` in regular position (`IsRegularPosition`) in a finite-dimensional normed algebra
`R` over a complete nontrivially normed field `F`, and computes their strict derivatives at
`0`. Coordinates `x = (y, s)` lie in `Coord F γ`: `y` in the image of the adjoint defect and
`s` in the centralizer subalgebra.

## Definitions

- `transverseCLM γ`, `centralCLM γ`: the continuous linear maps `(y, s) ↦ y` and
  `(y, s) ↦ s` into `R`.
- `productMap γ x = (1 + y)(1 + s) − 1`.
- `conjChart γ`: the Library's `normalizedOrbitChart` with conjugating part `1 + y` and
  centralizer part `1 + s`, that is `(1 + y)(1 + s) γ (1 + y)⁻¹ γ⁻¹` with the ring inverse
  (`conjChart_apply`). Thus `conjChart γ x` is the conjugate of `(1 + s) γ` by `1 + y`,
  multiplied by `γ⁻¹` on the right, and `conjChart γ 0 = 1` (`conjChart_zero`).
- `transverseDefect γ`: the adjoint defect restricted to its image, an endomorphism of the
  transverse space; `transverseDefect_bijective` shows it is bijective in regular position.
- `chartCoordEquiv hγ`: the linear equivalence `(y, s) ↦ (−(γ y γ⁻¹ − y), s)` of `Coord F γ`.
- `chartDerivative hγ`: `coordCLE ∘ chartCoordEquiv`, a continuous linear equivalence
  `Coord F γ ≃L[F] R` with `chartDerivative x = y + s − γ y γ⁻¹`
  (`chartDerivative_apply`).

## Results

- `mem_ker_defect_iff`: the kernel of the adjoint defect is the centralizer subalgebra.
- `hasStrictFDerivAt_productMap`: the strict derivative of `productMap γ` at `0` is
  `coordCLE hγ`, by the product rule.
- `hasStrictFDerivAt_conjChart`: for complete `R`, the strict derivative of `conjChart γ`
  at `0` is `chartDerivative hγ`. This specializes the Library's
  `Langlands.BaseChange.orbitChartDerivative` with the identity automorphism.

Bijectivity of `transverseDefect` holds because its kernel lies in the intersection of the
image of the defect with the centralizer, which is zero by complementarity, and because
every element `w` of the image is `d(w₁ + w₂) = d(w₁)` for its decomposition with `w₁`
transverse and `w₂` central.

## Role

The derivative `chartDerivative` is the linearization of ordinary conjugation at a regular
point. Its determinant in ambient coordinates is the Weyl discriminant
(`Langlands.Analysis.Local.WeylChartTranslate`, `Langlands.BaseChange.det_ordinaryWeylDifferential`),
as in Henniart–Lemaire (2011), II.2.10.
