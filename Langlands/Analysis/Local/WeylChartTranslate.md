# The local pushforward of the orbit map at an arbitrary base point

The module `Langlands.Analysis.Local.WeylChartTranslate` moves the local pushforward of
`Langlands.Analysis.Local.WeylChartLocal` from the base point `(T · 1, γ)` to an arbitrary
base point, and expresses the chart scale through a linear map of `R`. Here `F` and `R` are
as in `Langlands.Analysis.Local.WeylChartLocal`.

## Regular position and the ambient differential

- `isRegularPosition_of_isCompl`: if the kernel and the image of the adjoint defect are
  complementary, then `γ` is in regular position. The kernel is the centralizer subalgebra
  (`mem_ker_defect_iff`).
- `chartDifferential hγ = chartDerivative hγ ∘ coordCLE⁻¹`, the derivative of the
  conjugation chart in the coordinates of `R` itself.
- `chartDifferential_eq`: as a linear map, `chartDifferential = P − d`, where `d` is the
  adjoint defect and `P` the projection onto its kernel along its image. For `x = y + s` with
  `y` in the image and `s` in the kernel, both sides give `s − d y`.
- `chartScale_eq_of_map`: if `ringHaar` pushed forward by `chartDifferential` is `c • ringHaar`,
  then `chartScale = c`. The pushforward of `coordHaar` under `chartDerivative` is the
  pushforward of `ringHaar` under `chartDifferential`; compare masses of a ball of positive
  finite measure.

## Translation of the base point

- `orbitMap_rightTranslate`: for a commutative subgroup `H`, right translation of the coset
  by `g` conjugates the orbit map: `orbitMap (H x g, h) = g⁻¹ · orbitMap (H x, h) · g`.
- `exists_orbitMap_localPushforward_of_eq`: let `H` be a subgroup of `Rˣ` with commuting
  elements and `H = torusGroup γ`, with `γ` in regular position. Let `μ` be a left and right
  invariant Haar measure on `Rˣ`, `μT` a right invariant Haar measure on `H` and `ν`
  compatible with them (`IsCompatible`). For every `g₀ ∈ Rˣ`, every `t₀ ∈ H` with value `γ`
  and every neighbourhood `N` of `(H g₀, t₀)` there is an open `W ⊆ N` containing
  `(H g₀, t₀)` on which the orbit map is an open embedding and
  `((ν.prod μT).restrict W).map orbitMap = chartScale hγ • μ.restrict (orbitMap '' W)`.

For the proof, substitute `H = torusGroup γ` and apply `exists_orbitMap_localPushforward` to
the preimage of `N` under `Φ = (right translation by g₀) × id`. Take `W = Φ '' W'`. The
compatible measure `ν` is invariant under right translation (`IsCompatible.right_invariant`),
so `Φ` preserves `ν.prod μT`. The orbit map satisfies `orbitMap ∘ Φ = c ∘ orbitMap` with
`c u = g₀⁻¹ u g₀`, and `c` preserves `μ` by left and right invariance. The open embedding
property transfers through the homeomorphisms `Φ` and `c`.
