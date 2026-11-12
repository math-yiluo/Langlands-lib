# Finiteness of rational points in compact levels of a definite group

Author: Worker 19.

Let `σ` be an involution of a finite-dimensional `ℚ`-algebra `A` whose real
scalar extension `σ ⊗ ℝ` is positive. This module proves that the rational
similitudes whose diagonal image lies in a compact subgroup of the finite
adelic points form a finite set. In particular the arithmetic subgroup
`GJ(ℚ) ∩ g K g⁻¹` of a compact level `K` is finite, and each of its elements
has finite order.

This is the arithmetic input assumed by the predicate `RationalFiniteOrder`
of the module `HarrisLevelFreeSmall` (a separate candidate). This module
does not refer to that predicate; it states the finite-order property
directly.

## Source

Harris (1999) works with the group `GJ = GU(𝒟, *)` of a central simple
algebra `𝒟` with involution of the second kind. Section 1, printed p. 301
(PDF p. 3), defines

> `J = U(𝒟, *)`;  `GJ = GU(𝒟, *)`

with `GU(ℬ, *) = {g ∈ ℬ^× | g · g* ∈ G_{m,ℚ}}`, and among the hypotheses
following (1.1) requires

> `J_∞ ≅ ∏_{σ ∈ Σ_E} U(n)`,

so `J` is compact at infinity. Section 3, "The totally definite case",
printed p. 306 (PDF p. 8), begins: "Let `K ⊂ GJ(A^f)` be an open compact
subgroup".

Harris does not state the finiteness of `GJ(ℚ) ∩ g K g⁻¹`; it is a
standard consequence of definiteness. Definiteness enters here through the
positivity of `σ ⊗ ℝ`, the published `AlgebraInvolution.IsPositive` of
Worker 57 (`Langlands.Shimura.Unitary.Positivity`): Milne's condition
`Tr_{C/ℝ}(c* c) > 0` for nonzero `c` (Milne, *Introduction to Shimura
varieties*, Proposition 8.10(c) and Definition 8.11).

## Setting

- `σ : AlgebraInvolution ℚ A` with `A` finite over `ℚ`. `GJ(ℚ)` is the
  published `σ.similitudes`: pairs `(x, c) ∈ A^× × ℚ^×` with `x σ(x) = c`.
  This matches Harris's `g · g* ∈ G_m`.
- `GJ(A_f)` is the published `σ.FiniteAdelicPoints`, with the topology of
  `Langlands.Shimura.Unitary.Adelic`, and `σ.finiteAdelicDiagonal` is the
  diagonal map `GJ(ℚ) → GJ(A_f)`.
- The positivity hypothesis is `hpos : (σ.baseChange ℝ).IsPositive`.
- `integralFiniteAdeles K` is the published subring `∏_v 𝒪_v` of the finite
  adeles of a number field `K`.

## Declarations

### Bounded denominators (namespace `Langlands.Global`)

- `algebraMap_integer_mem_integralFiniteAdeles`: a global integer is integral
  at every finite place.
- `exists_mul_mem_integralFiniteAdeles`: every finite adele becomes integral
  after multiplication by a nonzero global integer. This repackages the
  published `exists_integer_mul_mem_adicCompletionIntegers`.
- `exists_mul_mem_integralFiniteAdeles_of_isCompact`: for a compact set `C`
  of finite adeles there is one nonzero global integer `d` with
  `d a ∈ ∏_v 𝒪_v` for all `a ∈ C`.
  - Proof: the translates `b + ∏_v 𝒪_v` (`b ∈ C`) are open and cover `C`.
    Choose a finite subcover `b₁, …, b_r` and integers `d_i` with
    `d_i b_i` integral, and take `d = ∏ d_i`. If `a - b_i` is integral, then
    `d a = d (a - b_i) + (∏_{j ≠ i} d_j) (d_i b_i)` is integral.
- `exists_intCast_eq_of_mem_integralFiniteAdeles`: a rational number that is
  integral at every finite place is an integer.
- `exists_intCast_mul_eq_of_isCompact`: for a compact set `C` of finite
  adeles of `ℚ` there is a nonzero integer `N` such that `N q ∈ ℤ` for every
  rational `q` whose diagonal image lies in `C`.
- `rat_den_dvd_natAbs_of_intCast_eq_mul`: if `N q ∈ ℤ` with `N ≠ 0`, the
  denominator of `q` divides `|N|`.
- `rat_eq_one_or_eq_neg_one_of_forall_zpow`: if `c ≠ 0` and `N c^k ∈ ℤ` for
  every integer `k`, then `c = 1` or `c = -1`.
  - Proof: if the denominator `D` of `c` is greater than `1`, then `D^{|N|}`
    divides `|N|`, which is impossible since `|N| < D^{|N|}`. So `c` is an
    integer. The same argument with `c⁻¹` shows that `|c|` (the denominator
    of `c⁻¹`) is `1`.
- `finite_setOf_rat_intCast_eq_mul_abs_le`: the rationals `q` with
  `N q ∈ ℤ` and `|q| ≤ M` form a finite set (they are among the `z / N` with
  `|z| ≤ ⌈|N| M⌉`).

### Positivity and finiteness (namespace `Langlands.Shimura.AlgebraInvolution`)

- `exists_abs_repr_le_of_isPositive`: let `b` be a `ℚ`-basis of `A`. There is
  a bound `M` such that for every `x ∈ A` and rational `c ≤ 1` with
  `σ(x) x = c`, all coordinates of `x` in `b` have absolute value at most `M`.
  - Proof: on `ℝ ⊗ A` with the basis `1 ⊗ b`, the function
    `Q(v) = Tr_ℝ(τ(y) y)` (with `y = Σ v_i (1 ⊗ b_i)` and `τ = σ ⊗ ℝ`) is a
    real quadratic form in the coordinates `v`, positive at every `v ≠ 0` by
    positivity. Its minimum `m` on the unit sphere of the sup norm is
    positive, so `m ‖v‖² ≤ Q(v)` by homogeneity. For `y = 1 ⊗ x` with
    `σ(x) x = c`, `Q(v) = c · dim_ℝ(ℝ ⊗ A) ≤ dim_ℝ(ℝ ⊗ A) = d`. Hence each
    coordinate satisfies `|v_i|² ≤ d / m`, and `|v_i| ≤ 1 + d / m`; `M` is the
    ceiling of `1 + d / m`.
- `finite_comap_finiteAdelicDiagonal`: if `σ ⊗ ℝ` is positive and `H` is a
  compact subgroup of `GJ(A_f)`, then the set of `γ ∈ GJ(ℚ)` whose diagonal
  image lies in `H` is finite.
  - Proof: the multiplier and the coordinates in a basis `b` of `A` (via the
    published `coordinateEquiv`) are continuous on `GJ(A_f)`, so their images
    of `H` are compact. By `exists_intCast_mul_eq_of_isCompact` the
    multipliers and the coordinates of rational points of `H` have
    denominators dividing fixed nonzero integers. Let `γ = (x, c)` have its
    image in `H`. All powers `γ^k` lie in `H` too, so all `c^k` have bounded
    denominators and `c = ±1`. In particular `c ≤ 1` and `σ(x) x = c`, so the
    coordinates of `x` are bounded by `exists_abs_repr_le_of_isPositive`.
    Thus `γ ↦ (coordinates of x, c)` maps the set injectively into the
    finite set of tuples of rationals with bounded denominators and bounded
    absolute values, times `{1, -1}`.
- `arithmeticSubgroup σ K g`: for a subgroup `K` of `GJ(A_f)` and
  `g ∈ GJ(A_f)`, the subgroup `GJ(ℚ) ∩ g K g⁻¹` of `GJ(ℚ)`: the preimage
  under the diagonal map of the conjugate `g K g⁻¹`.
  `mem_arithmeticSubgroup_iff`: `γ` belongs to it exactly when
  `g⁻¹ γ g ∈ K`.
- `finite_arithmeticSubgroup`: if `σ ⊗ ℝ` is positive and `K` is compact,
  then `GJ(ℚ) ∩ g K g⁻¹` is finite. The conjugate `g K g⁻¹` is compact as
  the image of `K` under a homeomorphism, so this is
  `finite_comap_finiteAdelicDiagonal`.
- `isOfFinOrder_of_conj_mem`: if `σ ⊗ ℝ` is positive, `K` is a compact
  subgroup of `GJ(A_f)`, `g ∈ GJ(A_f)`, and `g⁻¹ γ g ∈ K` for a rational
  similitude `γ`, then `γ` has finite order. Indeed `γ` lies in the finite
  group `arithmeticSubgroup σ K g`. Elements of a finite group have finite
  order, and the inclusion of the subgroup preserves this.

## Scope

- **Positivity is a hypothesis.** For Harris's `GJ`, positivity of the
  involution of `𝒟 ⊗ ℝ ≅ ∏_{σ ∈ Σ_E} M_n(ℂ)` is the standard reformulation
  of `J_∞ ≅ ∏ U(n)`; this module does not derive it. (The separate module
  `DefinitePositivity` derives it from the published `HasDefiniteSignature`.)
- **Compactness only.** Openness of `K` is not needed. The module does not
  prove finiteness of `GJ(ℚ)\GJ(A_f)/K` (Harris's finite set `_K S(GJ)`).
- **No link to `RationalFiniteOrder` here.** That predicate is defined in
  the module `HarrisLevelFreeSmall`, which is not a dependency here.
  `isOfFinOrder_of_conj_mem` is its content for compact `K`; the connection
  is made in `HarrisLevelFreePositive`.

## Provenance

The setting is Harris (1999), Sections 1 and 3, printed pp. 301 and 306,
read in the original (rendered pages). The positivity predicate is the
published one of Worker 57, following Milne's Proposition 8.10(c). The
finiteness of rational points in compact subgroups is a standard fact about
definite groups that Harris uses without statement; the statements in this
module and their proofs (bounded denominators by compactness, coordinate
bounds from the positive trace form, and the multiplier argument) are
written for this module.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (Milne's
  notes, through the published `Positivity`):
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.

Formal dependencies:

- the published `Langlands.Shimura.Unitary.Adelic` (`Points`,
  `Points.multiplier`, `Points.continuous_multiplier`, `coordinateEquiv`,
  `FiniteAdelicPoints`, `finiteAdelicDiagonal`), with `Similitude`
  (`similitudes`, `multiplier`, `mem_similitudes_iff`) and `Involution`
  (`baseChange`);
- the published `Langlands.Shimura.Unitary.Positivity` (`IsPositive`);
- the published `Langlands.Global.IntegralFiniteAdeles`
  (`integralFiniteAdeles`, `mem_integralFiniteAdeles`,
  `isOpen_integralFiniteAdeles`) and
  `Langlands.Global.AdeleQuotientCompactProof`
  (`exists_integer_mul_mem_adicCompletionIntegers`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.

The Mathlib results used include `IsCompact.elim_finite_subcover`,
`IsCompact.exists_isMinOn`, `isCompact_sphere`,
`HeightOneSpectrum.mem_integers_of_valuation_le_one`,
`Rat.ringOfIntegersEquiv`, `Rat.den_pow`, `Rat.den_inv_of_ne_zero`,
`Nat.lt_pow_self`, `Algebra.TensorProduct.basis`, `LinearMap.trace_id` and
`isOfFinOrder_of_finite`.
