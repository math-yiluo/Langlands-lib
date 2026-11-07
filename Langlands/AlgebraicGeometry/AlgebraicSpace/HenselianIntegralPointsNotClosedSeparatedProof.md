# A separated locally finite type space whose integral points are not closed

Author: Worker 105.

Proof of
`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosedOfSeparatedStatement.{u}`.
This is the counterexample showing that the closedness assertion of Corollary 5.7 of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
p.16, fails without quasi-compactness (finite type), even for separated spaces. The entry
theorem is `henselianIntegralPointsNotClosedOfSeparated`.

The target: let `K : Type u` be a nontrivially normed field whose closed unit ball is a
subring `O` (`∀ x, x ∈ O ↔ ‖x‖ ≤ 1`), with `HenselianLocalRing O`. Then there is an
algebraic space `X` over `Spec O` with `IsSeparated X` and `LocallyOfFiniteTypeOverBase X`
such that the range of `ι : X(O) → X_K(K)`,
`x ↦ (baseChangeRingPointsEquiv O K K X).symm (RingPoints.changeRing (Algebra.ofId O K) x)`,
is not closed for `etaleChartTopology K X_K`, where
`X_K = baseChange (Spec.algebraMap O K) X`.

The henselian hypothesis is not used.

## The example

Choose `p₀ ∈ K` with `0 < ‖p₀‖ < 1` (`NormedField.exists_norm_lt_one`); it lies in `O`, where
it is called `p`. Let `X` be the algebraic space of the scheme `DilatedLineChain.glued O p`:
the lines `Spec O[u_j]`, `j ∈ ℕ`, glued along `Spec O[t][1/p]` by `t = p^j + p^(j+1) u_j`.

1. The `O`-point `u_n = 0` of the line `n` has `t = pⁿ`. In `X_K(K)` it is the point
   `u_0 = s_n` of the line `0`, where `s_n = (p₀ⁿ - 1)/p₀`.
2. `s_n → c = -1/p₀`, and the points of the line `0` depend continuously on `u_0`.
3. The point `u_0 = c` (that is `t = 0`) is not in the range of `ι`. An `O`-point of `X` lies
   on some line `j` with coordinate `u_j ∈ O`, and `t = 0` forces `u_j = -1/p₀`, of norm
   `> 1`.

## Declarations

### Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosed`

- `isSeparated_schemeToSpace`: a scheme over `S` whose structure morphism is separated gives
  a separated algebraic space. This is the Library's `relative_diag_schemeYoneda` for closed
  immersions, in the same way as the Library's `isQuasiSeparated_schemeToSpace`.

### Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.DilatedLineChain`

Ring-theoretic lemmas, for a commutative ring `B`:

- `σ_ext`: two ring maps out of `L` that agree after composing with `σ j` are equal
  (`σ j = σ' j ∘ algebraMap`, with `σ' j` invertible).
- `exists_comp_σ`: a ring map `φ : R[X] → B` sending `p` to a unit factors as `ν ∘ σ j`
  (take `ν = lift φ ∘ τ' j`).
- `comp_σ_X` and `t_eq`: for `ω : L → B`, `ω(t) = ω(p)^j + ω(p)^(j+1) ω(u_j)`, using
  `ω(p) ω(e) = 1`.
- `isUnit_of_eq`: in a domain, if `π ≠ 0`, `i ≠ j` and
  `π^i + π^(i+1) α = π^j + π^(j+1) β`, then `π` is a unit. For `i < j`, cancel `π^i` to get
  `1 + π α = π^(j-i) (1 + π β)`, so `1 = π (π^(j-i-1)(1 + π β) - α)`.

The scheme over `Spec R`:

- `overBase R p`, `chart R p j` (the line `j` over `Spec R`), `chart_left`, and
  `chartPoint R p j q = q ≫ chart R p j`, typed as a `RingPoint`.
- Instances `QuasiSeparatedSpace (glued R p)` (`CommonOpenGluing.quasiSeparatedSpace`) and
  `quasiSeparated_hom` (`quasiSeparated_iff_quasiSeparatedSpace`, the base being affine).
- `locallyOfFiniteType_hom`: `IsZariskiLocalAtSource.of_openCover` on the gluing cover.
- `eq_of_comp_eq`: let `V` be a local domain and `F` a field with `V → F` injective. Two
  morphisms `l₁ l₂ : Spec V ⟶ glued R p` that agree after `Spec F → Spec V` are equal. By
  `CommonOpenGluing.exists_lift_of_isLocalRing`, `l₁ = a ≫ ι i` and `l₂ = b ≫ ι j`, with
  `a = Spec α'` and `b = Spec β'`.
  - If `i = j`, cancel the monomorphism `ι i`. Then `α'` and `β'` agree after `V → F`, hence
    agree.
  - If `i ≠ j`, `CommonOpenGluing.exists_of_comp_eq` gives `w : Spec F ⟶ Spec L` through
    which both generic points factor. Let `ω = Spec.preimage w`. Then `ω ∘ σ i` and
    `ω ∘ σ j` are `α'` and `β'` followed by `V → F`. So `α'` and `β'` agree on `p`; call
    the common value `π`. It is nonzero, since `ω(p)` is a unit. By `t_eq`,
    `π^i + π^(i+1) α'(X) = π^j + π^(j+1) β'(X)` in `V`. So `π` is a unit (`isUnit_of_eq`),
    and `α'`, `β'` factor through `σ i`, `σ j` (`exists_comp_σ`) as `νa`, `νb`. Both
    `νa` and `νb`, followed by `V → F`, equal `ω` (`σ_ext`), so `νa = νb`. Then
    `l₁ = Spec νa ≫ g i ≫ ι i = Spec νb ≫ g j ≫ ι j = l₂` by `CommonOpenGluing.g_ι`.
- `isSeparated_hom`: the structure morphism is separated, by Mathlib's valuative criterion
  `IsSeparated.of_valuativeCriterion` (it is quasi-separated). Two lifts in a valuative
  square agree on the fraction field, so `eq_of_comp_eq` applies.
- `isSeparated` and `locallyOfFiniteTypeOverBase`: the associated algebraic space is
  separated (`isSeparated_schemeToSpace`) and locally of finite type
  (`HasAtlasProperty.of_scheme`).
- Instances: each `(chart R p j).left` is an open immersion, and `chart R p j` is a
  monomorphism.
- `exists_chart_factor`: over a local ring `S`, every `S`-point of the glued scheme is
  `a ≫ chart R p j` for a line `j` and a point `a` of `Spec R[X]`.
- `t_eq_of_chart_eq`: for an `R`-algebra `B`, if the point `u_i = α` of the line `i` equals
  the point `u_j = s` of the line `j`, then
  `p^i + p^(i+1) α = p^j + p^(j+1) s` in `B`. For `i = j`, cancel the monomorphism and read
  off the coordinate (`affineRingPointEquiv_ringTestMap`). For `i ≠ j`, factor through the
  common open (`CommonOpenGluing.exists_of_comp_eq`) and apply `t_eq` to
  `ω = Spec.preimage w`.
- `chart_eq_of_t_eq`: conversely, if `p` is a unit in `B` and the two values of `t` agree,
  the two points are equal. Evaluation at that common value `t₀` extends to `ω : L → B`, and
  `ω ∘ σ i`, `ω ∘ σ j` are evaluations at `α` and `s`. Then use `CommonOpenGluing.g_ι`.

### Helpers from `HenselianIntegralPointsNotClosedCharts`

The proof uses `linePoint`, `eq_linePoint`, `affineRingPointEquiv_ringTestMap`,
`baseChangeChart`, `baseChangeRingPointsEquiv_baseChangeChart_pointMap` and
`continuous_linePoint`, described in that module's Markdown.

### Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`

- `henselianIntegralPointsNotClosedOfSeparated : HenselianIntegralPointsNotClosedOfSeparatedStatement.{u}`.

## Proof of `henselianIntegralPointsNotClosedOfSeparated`

Let `X` be the space of `overBase O p`; it is separated and locally of finite type.

1. **Chart map.** `f = (schemeToSpace _).map (chart O p 0)` is étale (`isEtale_map`; open
   immersions are étale). Let `d = baseChangeChart K (ringTest O O[X]) f` and
   `Φ(s) = d.pointMap (ringPointBaseChangeEquiv O K K _ (linePoint O s))`.
2. **Continuity.** `Φ` is continuous (`EtaleFiniteTypeChart.continuous_pointMap`,
   `schemeBaseChangeTopology_proof`, `continuous_linePoint`).
3. **Reading `Φ`.** `baseChangeRingPointsEquiv O K K X (Φ s)` is the `K`-point
   `chartPoint O p 0 (linePoint O s)` (`baseChangeRingPointsEquiv_baseChangeChart_pointMap`).
4. **The limit point is not in the range.** Let `c = -p₀⁻¹` and suppose `ι x = Φ c`. Then
   `ringTestMap O (Algebra.ofId O K) ≫ x = chartPoint O p 0 (linePoint O c)` as `K`-points of
   the scheme. By `exists_chart_factor`, `x = a ≫ chart O p j`, and `a = linePoint O α₀` with
   `α₀ ∈ O` (`eq_linePoint`). Viewed in `K` this is `linePoint O α₀` (`ringTestMap_comp`).
   `t_eq_of_chart_eq` gives `p₀^j (1 + p₀ α₀) = 1 + p₀ c = 0`, so `α₀ = -p₀⁻¹`. This
   contradicts `‖α₀‖ ≤ 1 < ‖p₀‖⁻¹`.
5. **The sequence.** For every `n`, `Φ(s_n) = ι x_n` for the `O`-point
   `x_n = chartPoint O p n (linePoint O 0)`. After the same identifications this is
   `chart_eq_of_t_eq` with `p₀` a unit in `K` and `p₀ⁿ + p₀ⁿ⁺¹ · 0 = 1 + p₀ s_n`.
6. **Conclusion.** `s_n → c`, since `p₀ⁿ → 0` (`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`).
   So `Φ(s_n) → Φ(c)`. If the range were closed it would contain `Φ(c)`
   (`IsClosed.mem_of_tendsto`), contradicting step 4.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Corollary 5.7,
  printed p.16. Conrad states closedness of the image for quasi-separated spaces locally
  of finite type; the example shows that quasi-compactness is needed even for separated
  spaces.
- The example (a chain of dilatations of the affine line whose integral discs accumulate at
  a non-integral point) is an internal construction by Worker 105 for this proof.
