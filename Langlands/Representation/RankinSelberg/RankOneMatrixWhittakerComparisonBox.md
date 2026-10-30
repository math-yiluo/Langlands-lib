# Every reduced rank-one value is a matrix–Whittaker value

Module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox`.
This is a helper module for the positive-rank branch (`n = m + 1`) of the proof of
the published statement
`Langlands.RankinSelberg.RankOneMatrixWhittakerComparisonStatement`. It proves one
of the two inclusions of the positive-rank identification. The other inclusion is
proved in a separate module.

## Main result

`Langlands.RankinSelberg.rankOneModelValues_subset_whittakerRationalValues p F ψ m V σ`
uses the canonical topology, valuation and local-field structure of the `p`-adic
field `F`, and the Borel σ-algebra on `GL₁`. It states

```text
IsSmooth σ → ∀ ℓ : glFunctionals ψ (m + 1) σ,
  rankOneModelValues F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier 0) σ ℓ
    ⊆ GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ.
```

Here `σ` acts on `GL(m + 1 + 1)` and `ℓ` is a standard Whittaker functional. The
left side is the set of rational functions (definitions module
`RankOneMatrixWhittakerComparisonValues`) that continue an integral

```text
Ψ(s, W) = ∫ W(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2) dg      (g ∈ GL₁)
```

for some model function `W` of `ℓ`, when the integral converges absolutely on a
right half-plane. The right side is the published set of shifted rational values of
the matrix integrals `Z(Φ, s + (m+1)/2, W) = ∫ Φ(g) W(g) |det g|^(s + (m+1)/2) dg`
of model functions of the same `ℓ`. These integrals must converge absolutely on a
right half-plane. The measures are `generalLinearHaar`, normalized by `GL(O)` of mass
one.

The proof is
`RankOneBox.rankOneModelValues_subset`, a consequence of the box computation below.
Take `R` with witness `W` and convergence for `re s > a₀`. The box computation gives
`Φ₀` and `C > 0`. Replace `W` by the model function `C⁻¹ W` (the model vector
`C⁻¹ • w`). Then for `re s > a₀` the matrix integral converges, and it equals
`Ψ(s, W)`. So the rational continuation of `Ψ(·, W)` on some half-plane
`re s > a₁` is one for the matrix integrals on `re s > max a₀ a₁`.

## The box computation

`RankOneBox.exists_box_constant F ψ σ ℓ w hσ` gives a matrix Schwartz–Bruhat
function `Φ₀` and a real `C > 0`. For every `s` where `Ψ(s, W)` converges
absolutely, it shows that

```text
Z(Φ₀, s + (m+1)/2, W) converges absolutely and equals C · Ψ(s, W).
```

`Φ₀` and `C` depend on `W` but not on `s`.

### Choices

Write `𝓛 c = π^(-c) O` for the additive lattice `additiveLattice c`, and `𝔪ᵃ` for the
image of the `a`-th power of the maximal ideal (`levelSet F a`).

- `A = max A₀ 0`, where `A₀` comes from `exists_rankOneEmbedding_support` (module
  `RankOneMatrixWhittakerComparisonSupport`). `W(diag(det g, 1, …, 1)) ≠ 0` implies
  `det g ∈ 𝓛 A`.
- `q = min (n(ψ)) 0`, with `n(ψ)` the additive conductor. So `ψ = 1` on `𝓛 q`.
- `a > 0`, from `exists_pos_principalLevelOpenSubgroup_subset`. The principal
  congruence subgroup `L = K(a)` fixes `w`, by smoothness of the model
  (`glModel_isSmooth`). Also every `y ∈ L` has `y₀ⱼ ∈ 𝓛 (q - A)` for `j ≠ 0`.
  It follows that `𝔪ᵃ ⊆ 𝓛 q`, from the transvection `1 + z E₀₁ ∈ L`.
- The box `box F A q a` is the set of matrices `X` with

  ```text
  X₀₀ ∈ 𝓛 A,   X₀ⱼ ∈ 𝓛 q (j ≠ 0),   Xᵢⱼ − δᵢⱼ ∈ 𝔪ᵃ (i ≠ 0).
  ```

  It is compact and open (`isCompact_box`, `isOpen_box`). Its indicator is
  `Φ₀ = compactOpenIndicator (box F A q a) …`, from `LastRowCompactOrbitProof`.

### Algebraic facts

- `mul_mem_box_iff`: `X y ∈ box ↔ X ∈ box` for `y ∈ L`, by entrywise lattice
  estimates.
- `exists_mem_principalLevel_mul_inv_upper`: for invertible `g` in the box, the
  matrix `Y` equal to `g` with first row replaced by `e₀` lies in `L`
  (`exists_mem_principalLevelSubgroup`), and `g Y⁻¹` is upper triangular, since it
  equals the identity outside the first row.
- `exists_point_mul_of_mem_box`: if `k ∈ K = GL(O)` and `point x₀ · k` lies in the
  box, then `k = point x_β · y` with `y ∈ L` and the torus coordinate of `x_β`
  consisting of valuation-one units. Here `β = k y⁻¹` is upper triangular and
  integral, and `exists_point_eq` writes it as a parametrization point.
- `point_eq_mul`: `point((g, t), u) = u · diag(det g, 1, …, 1) · diag((∏ t)⁻¹, t)`.
  For `t` in the torus box (`tᵢ ≡ 1 mod 𝔪ᵃ`), the last factor lies in `L`
  (`torusFactor_mem`, via the subgroup `unitLevel`).
- `mem_box_unipotent_mul_iff`: `u · diag(det g, 1, …, 1)` lies in the box exactly
  when `det g ∈ 𝓛 A` and `u` lies in the unipotent box `unipotentBox F q a`. The
  unipotent box is `u₀ⱼ ∈ 𝓛 q` (`j ≠ 0`) and `uᵢⱼ − δᵢⱼ ∈ 𝔪ᵃ` (`i ≠ 0`). The
  standard character is trivial on it (`standardCharacter_eq_one`).

### Integration

The integration uses the Iwasawa parametrization `point((g, t), u) = u · D(g, t)`
and the measure `iwasawaMeasure` of the helper module `RankOneMatrixIwasawa`, which
is copied unchanged.

- `measurePreserving_rshift`: right translation `rshift x_β` of parameters, with
  `point (rshift x_β x) = point x · point x_β`, preserves `iwasawaMeasure` when the
  torus coordinate of `x_β` consists of units. On the base `GL₁ × (Fˣ)ⁿ`, which is
  commutative, it is a translation whose density factor `ω(b_β)⁻¹` is `1`
  (`map_mul_left_withDensity`, `torusModulus_eq_one`). On the fibre it is a right
  translation of `unipotentHaar` (`unipotentHaar_isMulRightInvariant`). The two
  combine with `MeasurePreserving.skew_product`.
- `lintegral_enorm_eq_of_support` and `integral_eq_of_support` treat a continuous
  `H` on `GL(n+1)` and a measurable `S`. Suppose that for `k ∈ K ∩ S` the function
  `x ↦ H(point x · k)` is `H ∘ point` composed with a measure-preserving map, and
  that it vanishes for `k ∈ K \ S`. Then
  `∫_G H = dk(S) · ∫_X H(point x) dx`, from `map_iwasawaMeasure_prod`, Tonelli
  and Fubini. The Lebesgue version needs no integrability. The Bochner version
  assumes `H` integrable.
- `boxSupport` is the set `S` of `k ∈ K` with `point x₀ · k` in the box for some
  `x₀`. It is open, contains `1`, and `0 < dk(S) ≤ 1`.
- `matrixIntegrand_point`: at `x = ((g, t), u)`, the box integrand equals
  `W(diag(det g, 1, …, 1)) |det g|^s · 1_torusBox(t) · 1_unipotentBox(u)`. If
  `det g ∉ 𝓛 A`, both sides vanish by the support bound.
- `integral_param_of_eq` and `lintegral_param_of_eq` factor the parameter integral
  as a `GL₁` integral times the masses of the two boxes (`integral_prod_mul`,
  `lintegral_prod_mul`, `parameterMeasure_eq_prod`).
- `weight_smul_integrand`: the `GL₁` density `|det g|^(-(m+1))` of `glOneMeasure`
  turns `|det g|^(s + (m+1)/2)` into `|det g|^(s - (m+1)/2)`.
- The masses are finite and positive. `tailMeasure_torusBox` gives
  `μ×(1 + 𝔪ᵃ)^(m+1)`, with `0 < μ×(1 + 𝔪ᵃ) ≤ μ×(O^×) = 1`. The unipotent box is
  open, contains `1`, and lies in `N(O)`, which has mass one.

The resulting constant is
`C = dk(S) · tail(torusBox) · N(unipotentBox)`. With `H = Φ₀ W |det|^(s + (m+1)/2)`,
the Lebesgue identity gives
`∫ ‖H‖ = dk(S) · ∫ ‖Ψ-integrand‖ · tail · N < ∞`. So `H` is integrable, and the
Bochner identity gives `Z = C · Ψ(s, W)`.

## Provenance

The inclusion is half of the identification `I₁ = I₃` in JPSS 1983, §5.2, which
cites JPS 1979, Theorem (4.3) and Remark (4.2). The route follows JPS 1979,
Lemma (4.3.4) and the end of the proof of (4.3) (Ann. of Math. 109, printed
pp. 192–194). Those steps are a characteristic function `Φ` of a compact open set
of matrices, the reduction of `k ∈ K` to `(B ∩ K) K_m`, the right `B ∩ K`
invariance of the measure on `B`, and the explicit factorization of the resulting
integral.

The implemented proof differs from JPS in three ways.

- The set differs. JPS take `x₁₁ ∈ 𝔭^(-m)`, `xⱼⱼ ∈ 1 + 𝔭^m` (`j ≥ 2`), integral
  entries above the diagonal and entries in `𝔭^m` below it. Here the first row is
  `(𝓛 A, 𝓛 q, …, 𝓛 q)` and the other rows are congruent to the identity mod `𝔪ᵃ`.
  With this choice the reduction to `(B ∩ K) L` is the elementary row replacement
  above, instead of the exterior-power argument of JPS. It also makes the standard
  character trivial on the unipotent box.
- `W` itself appears, not a `K_m`-average `W'`, because `W` is fixed by `L`.
- The measures are the Library's normalized Haar measures, and the constant `C` is
  explicit.

The module asserts nothing about the reverse inclusion or about the Laurent modules
`I₁`, `I₃`.

The parameter commutativity proof reuses `rankOne_mul_comm` from
[RankOneQuotient](RankOneQuotient.md); diagonal conjugation is the shared
`diagonalConj` from [DiagonalUnipotentHaar](DiagonalUnipotentHaar.md).
