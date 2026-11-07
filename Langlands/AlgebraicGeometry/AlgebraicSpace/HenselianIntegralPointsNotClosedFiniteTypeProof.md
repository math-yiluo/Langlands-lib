# A quasi-separated finite type space whose integral points are not closed

Author: Worker 105.

Proof of
`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosedOfFiniteTypeStatement.{u}`.
This is the counterexample showing that the closedness assertion of Corollary 5.7 of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
p.16, fails without separatedness. The entry theorem is
`henselianIntegralPointsNotClosedOfFiniteType`.

The target: let `K : Type u` be a nontrivially normed field whose closed unit ball is a
subring `O` (`∀ x, x ∈ O ↔ ‖x‖ ≤ 1`), with `HenselianLocalRing O`. Then there is an
algebraic space `X` over `Spec O` with `IsQuasiSeparated X` and `FiniteTypeOverRing O X`
such that the range of `ι : X(O) → X_K(K)`,
`x ↦ (baseChangeRingPointsEquiv O K K X).symm (RingPoints.changeRing (Algebra.ofId O K) x)`,
is not closed for `etaleChartTopology K X_K`, where
`X_K = baseChange (Spec.algebraMap O K) X`.

The henselian hypothesis is not used.

## The example

Choose `p₀ ∈ K` with `0 < ‖p₀‖ < 1` (`NormedField.exists_norm_lt_one`). It lies in `O`; call
it `p` there. Let `X` be the algebraic space of the scheme `DoubledPointLine.glued O p` over
`Spec O`. It is `Spec O[t]` (chart `true`) and `Spec O[s]` (chart `false`) glued along `D(p t)`
and `D(p (p s - 1))` by `t = p s - 1`. Informally, its generic fibre is the affine line with
the origin `t = 0` doubled by the point `s = 1/p`.

Let `c = p₀⁻¹` and `s_n = c (1 + p₀ⁿ)`. Then:

1. the `O`-points `t = pⁿ` of chart `true` have the same image in `X_K(K)` as the points
   `s = s_n` of chart `false`;
2. `s_n → c` in `K`, and the points `s` of chart `false` depend continuously on `s` in
   `X_K(K)`;
3. the point `s = c` of chart `false` is not in the range of `ι`.

So that point is a limit of points of the range but not in it, and the range is not closed.

## Declarations

### Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.DoubledPointLine`

For a commutative ring `R` and `p ∈ R`:

- `overBase R p`: the glued scheme as an object of `Over (Spec R)`, with structure morphism
  `toBase`. `chart R p b : ringTest R R[X] ⟶ overBase R p` is the chart `ι R p b` as a
  morphism over `Spec R`.
- Instances `QuasiSeparatedSpace (glued R p)` (`CommonOpenGluing.quasiSeparatedSpace`: the
  charts are affine and the common open `Spec B₂` is quasi-compact) and
  `CompactSpace (glued R p)` (union of two compact chart images).
- `quasiSeparated_hom`, `quasiCompact_hom`, `locallyOfFiniteType_hom`: the structure
  morphism is quasi-separated (`quasiSeparated_iff_quasiSeparatedSpace`, the base being
  affine), quasi-compact (`quasiCompact_of_compactSpace`) and locally of finite type
  (`IsZariskiLocalAtSource.of_openCover` on the gluing cover; each chart is
  `Spec R[X] → Spec R`).
- `isQuasiSeparated`: the associated algebraic space is quasi-separated
  (`isQuasiSeparated_schemeToSpace`).
- `finiteTypeOverRing`: the associated algebraic space is of finite type over `R`
  (`HasAtlasProperty.of_scheme`).
- `chartPoint R p b q = q ≫ chart R p b`: the point of the glued scheme given by a point `q`
  of chart `b`, typed as a `RingPoint` like `linePoint` (from
  `HenselianIntegralPointsNotClosedCharts`).
- `exists_chart_factor`: over a local ring `S`, every `S`-point `x` of the glued scheme is
  `a ≫ chart R p b` for some chart `b` and some point `a` of `Spec R[X]`
  (`CommonOpenGluing.exists_lift_of_isLocalRing`, made a morphism over `Spec R` with
  `ι_toBase`).
- `ringTestMap_aeval_chart_eq`: for an `R`-algebra `T` and `s ∈ T` with `p (p s - 1)` a unit,
  the point `t = p s - 1` of chart `true` equals the point `s` of chart `false`. Evaluation
  at `s` extends to `ω : B₂ → T` (`IsLocalization.Away.lift`). Then `Spec ω ≫ g₂` is the
  point `s`, and `Spec ω ≫ g₁` is the point `t`, since `ω ∘ α` sends `t` to `p s - 1`. The
  two composites agree in the glued scheme by `CommonOpenGluing.g_ι`.
- `chart_true_ne`: for a nontrivial `R`-algebra `T` and `c ∈ T` with `p c = 1`, no point
  of chart `true` equals the point `s = c` of chart `false`. Otherwise
  `CommonOpenGluing.exists_of_comp_eq` gives `w : Spec T → Spec B₂` with `w ≫ g₂` the point
  `s = c`. So `ω = Spec.preimage w` sends `f₂ = p (p s - 1)` to `p (p c - 1) = 0`, but `f₂` is
  a unit in `B₂`.
- `algebraMap_eq_of_chart_false`: if an `R`-point `a` of chart `false`, viewed in `T`, is the
  point `s = c` of chart `false`, then the coordinate of `a` maps to `c`. Cancel the
  monomorphism `chart R p false` (an open immersion), write `a = ringTestMap R φ`, and
  evaluate at `X`.

### Helpers from `HenselianIntegralPointsNotClosedCharts`

The proof uses `linePoint`, `affineRingPointEquiv_ringTestMap`, `baseChangeChart`,
`baseChangeRingPointsEquiv_baseChangeChart_pointMap` and `continuous_linePoint` from the
helper module `HenselianIntegralPointsNotClosedCharts` (namespace
`HenselianIntegralPointsNotClosed`), described in its Markdown.

### Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`

- `henselianIntegralPointsNotClosedOfFiniteType : HenselianIntegralPointsNotClosedOfFiniteTypeStatement.{u}`.

## Proof of `henselianIntegralPointsNotClosedOfFiniteType`

Let `X` be the space of `overBase O p`; it is quasi-separated and of finite type by
`isQuasiSeparated` and `finiteTypeOverRing`.

1. **Chart map.** `f = (schemeToSpace _).map (chart O p false)` is étale (`isEtale_map`,
   open immersions are étale). Let `d = baseChangeChart K (ringTest O O[X]) f`, and
   `Φ(s) = d.pointMap (ringPointBaseChangeEquiv O K K _ (linePoint O s))` for `s ∈ K`.
2. **Continuity.** `Φ` is continuous: `d.pointMap` is continuous for the étale-chart
   topology (`EtaleFiniteTypeChart.continuous_pointMap`), `ringPointBaseChangeEquiv` is a
   homeomorphism for the scheme point topologies (`schemeBaseChangeTopology_proof`), and
   `continuous_linePoint`.
3. **Reading `Φ`.** `baseChangeRingPointsEquiv O K K X (Φ s)` is the `K`-point
   `chartPoint O p false (linePoint O s)` of `X`
   (`baseChangeRingPointsEquiv_baseChangeChart_pointMap`).
4. **The limit point is not in the range.** Suppose `ι x = Φ c`. Applying
   `baseChangeRingPointsEquiv` and `schemeRingPointsEquiv`,
   `ringTestMap O (Algebra.ofId O K) ≫ x = chartPoint O p false (linePoint O c)` as `K`-points
   of the scheme. By `exists_chart_factor` (`O` is local), `x = a ≫ chart O p b`.
   - `b = false`: `algebraMap_eq_of_chart_false` shows that the coordinate of `a`, an
     element of `O`, maps to `c`. So `‖c‖ ≤ 1`, whereas `‖c‖ = ‖p₀‖⁻¹ > 1`.
   - `b = true`: this contradicts `chart_true_ne`, since `p c = 1`.
5. **The sequence.** For every `n`, `Φ(s_n) = ι x_n` with `x_n` the `O`-point
   `chartPoint O p true (linePoint O (pⁿ))`. After the same identifications this says that the
   point `t = pⁿ` of chart `true`, viewed in `K`, is the point `s = s_n` of chart `false`.
   That is `ringTestMap_aeval_chart_eq` at `s = s_n`: here `p s_n - 1 = p₀ⁿ` and
   `p (p s_n - 1) = p₀ⁿ⁺¹ ≠ 0`. The composite `Algebra.ofId O K ∘ aeval pⁿ` is rewritten as
   `aeval (p₀ⁿ)` with `ringTestMap_comp`.
6. **Conclusion.** `s_n → c`, since `p₀ⁿ → 0` (`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`).
   So `Φ(s_n) → Φ(c)`. If the range were closed it would contain `Φ(c)`
   (`IsClosed.mem_of_tendsto`), contradicting step 4.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Corollary 5.7,
  printed p.16. Conrad states closedness of the image for quasi-separated spaces locally
  of finite type; the example shows that separatedness is needed.
- The example (an affine line with a doubled point, where integral points of one origin
  converge to the other) is an internal construction by Worker 105 for this proof.
