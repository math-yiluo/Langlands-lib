# Compact projection along the orthogonal matrix group

Write `H = GL_(r+1)(ℝ)`, `O = Matrix.unitaryGroup (Fin (r+1)) ℝ` for the group of orthogonal
`(r+1) × (r+1)` real matrices and `Kc = unitaryCompact ℝ (r+1)` for the orthogonal subgroup of
`H`. The module proves `RealOrthogonalCompactProjectionPremise r` of
`RealAdjacentCanonicalChamber` at every rank, from the compact projection theorem
`realExactCompactProjection` of `RealExactCompactProjection`, which is stated for `Kc`.

## Results

- `orthogonalUnitaryCompactEquiv n`: the isomorphism of topological groups `O ≃ₜ* Kc` sending a
  unitary matrix `k` to `Unitary.toUnits k`, the same matrix seen as an invertible matrix. Its
  inverse is `unitaryCompactMatrix ℝ n` of `SmoothKFiniteAdmissibility`; the forward map is
  continuous by `continuous_unitary_toUnits`. `orthogonalUnitaryCompactEquiv_apply_val` records
  that the underlying invertible matrix of the image of `k` is `Unitary.toUnits k`.

- `realOrthogonalCompactProjectionPremise r : RealOrthogonalCompactProjectionPremise r`. For a
  block list `es`, `a ∈ ℝˣ`, a continuous weight `κ` on `O` whose left translates
  `k ↦ κ(x⁻¹ k)` span a finite-dimensional space, a uniform real Whittaker map `B` of character
  `a` on the compact-finite standard module of `es`, a vector `f` of that module and `g ∈ H`,
  there is a vector `p` of the module with
  `p(x) = ∫_O κ(k) f(x k g) dk` for every orthogonal `x` and
  `B p(x) = ∫_O κ(k) B f(x k g) dk` for every `x ∈ H`,
  the integrals taken for the Haar measure `Measure.haar` of `O`.

## Proof

Let `e = orthogonalUnitaryCompactEquiv (r+1)`, equip `Kc` with its Borel σ-algebra, and let `ν` be
the image under `e` of the Haar measure of `O`. It is a Haar measure on `Kc`
(`ContinuousMulEquiv.isHaarMeasure_map`). The weight `κ' = κ ∘ e⁻¹` is continuous on `Kc`. Since
`e⁻¹(h⁻¹ k) = e⁻¹(h)⁻¹ e⁻¹(k)`, each left translate of `κ'` is the composite with `e⁻¹` of a left
translate of `κ`. So the span of the left translates of `κ'` lies in the image of the span of the
left translates of `κ` under the linear map `φ ↦ φ ∘ e⁻¹` (`LinearMap.funLeft`), and it is
finite-dimensional.

A uniform real Whittaker map is in particular a real Whittaker intertwiner (the first conjunct
of `IsRealUniformWhittakerIntertwiner`). Then `realExactCompactProjection` with `ν`, `κ'`, `B`,
`f` and `g` gives a vector `p` with `p(x) = ∫_Kc κ'(k) f(x k g) dν(k)` and
`B p(x) = ∫_Kc κ'(k) B f(x k g) dν(k)` for every `x ∈ H`. As `e` is a homeomorphism, it is a
measurable embedding, so integrals for `ν` are integrals for the Haar measure of `O` after
composition with `e` (`MeasurableEmbedding.integral_map`). Since `κ'(e k) = κ(k)` and the matrix of
`e k` is `Unitary.toUnits k`, these are the two required identities; the first is used only at
orthogonal `x`.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, §8.3, pp. 59–60, averages `W'(x k h)` against an
elementary idempotent of the maximal compact subgroup `K_(n−1)` and writes the result as a finite
sum. This module only identifies the two models of that compact group used in the Library, the
orthogonal matrix group and the orthogonal subgroup of `GL_(r+1)(ℝ)`, together with their Haar
measures.
