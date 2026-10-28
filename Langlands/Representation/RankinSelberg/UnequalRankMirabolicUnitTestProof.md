# Compact mirabolic unit tests for every unequal-rank JPSS block: proof

Author: Worker 856.

This module proves the published proposition
`Langlands.RankinSelberg.UnequalRankMirabolicUnitTestStatement.{uF,uW} F T n j k`
of [UnequalRankMirabolicUnitTestStatement](UnequalRankMirabolicUnitTestStatement.md).
It changes neither that statement nor anything it imports. The closing theorem
`Langlands.RankinSelberg.unequalRankMirabolicUnitTest` has the complete type

```lean
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ),
  Langlands.RankinSelberg.UnequalRankMirabolicUnitTestStatement.{uF, uW} F T n j k
```

The universes `uF` and `uW` stay independent. The proof works with the
supplied realization `T` throughout. It covers every unitary additive
character `ψ`, and every quotient measure `μ` compatible with the actual
general-linear and unipotent Haar measures. It covers every additive Haar
measure `ν` and every representation `σ` of Whittaker type. It also covers
every nonzero actual inverse functional `ℓ'`. No case split on `n`, `j` or
`k` is made; in particular `j = 0` is handled by the same argument (see
*Rectangular masses* below). The only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Notation

Write `t = n + 1` for the smaller rank and `r = n + (j + k + 1)`, so the larger
group is `GL_(r+1)`. The block matrix is the existing
`unequalRankMatrix j k g x`. Its entries are `[g, 0, 0]` in the first `t`
rows, `[x, 1_j, 0]` in the next `j` rows, and `[0, 0, 1]` below. For a level
`a`, write `K_t(a) = Conductor.principalLevelSubgroup F n a` and
`K_r(a) = Conductor.principalLevelSubgroup F r a`. These are the published
principal congruence subgroups `1 + 𝔪^a M(O)` of the valuation integers `O`
of the supplied valuative relation. Write `N_t` and `N_r` for the actual upper
unipotent subgroups and `P_r` for the actual mirabolic subgroup of `GL_(r+1)`.

## Helper declarations

All helpers live in the namespace
`Langlands.RankinSelberg.UnequalRankMirabolicUnitTest`. They are internal to
this proof and are not results stated in JPSS.

### Algebra

- `levelSet F a : Set F` is the image in `F` of the ideal `𝔪^a` of the
  valuation integers `O`. The lemmas `zero_mem_levelSet`, `add_mem_levelSet`,
  `neg_mem_levelSet` and `sum_mem_levelSet` give closure under `0`, sums,
  negation and finite sums. `mul_mem_levelSet` gives closure under
  multiplication by an integral element. `levelSet_eq_image` restates the
  definition as an image under `Subtype.val`. The lemma
  `mem_integer_of_mem_levelSet` says elements of the level set are integral.
  `mem_integer_of_sub_one_mem_levelSet` says the same for an entry congruent
  to an identity-matrix entry.
- `mem_principalLevelSubgroup_iff` restates the published
  `Conductor.mem_principalCongruenceSubgroup_iff` in terms of `levelSet`.
  An invertible matrix `g` lies in `K(a)` exactly when every entry of
  `g - 1` and of `g⁻¹ - 1` lies in `levelSet F a`.
- `exists_mem_principalLevelSubgroup`: for `0 < a`, every matrix `Y` with all
  entries of `Y - 1` in `levelSet F a` is the underlying matrix of an element
  of `K(a)`. Only the entries of `Y` are assumed. The entries are lifted to
  an integral matrix `Z ≡ 1 mod 𝔪^a`. Reducing modulo `𝔪^a` and applying
  `RingHom.map_det` gives `det Z ≡ 1 mod 𝔪^a`. Since `a > 0`, the ideal
  `𝔪^a` lies in `𝔪`, so `det Z ∉ 𝔪`. Hence `det Z` is a unit of the local
  ring `O`, and `Z` is an integral unit. The published
  `Conductor.map_mem_principalCongruenceSubgroup` and
  `Conductor.mem_integralPrincipalCongruence` put its image in `K(a)`.

### Blocks

- `sum_dite_lt`: a sum over `Fin N` of terms that vanish from index `t ≤ N`
  on equals the corresponding sum over `Fin t`.
- `unequalRankMatrix_apply_top` and `unequalRankMatrix_apply_mid` compute
  the entries of the leading `t` rows and of the `j` rectangular rows of the
  block matrix. They follow from the published `unequalRankMatrix_val`,
  `appendIdentity_entry` and `rectangularEntries`.
- `unequalRankMatrix_mem` (block membership): if `0 < a`, `g ∈ K_t(a)` and
  every entry of `x` lies in `levelSet F a`, then
  `unequalRankMatrix j k g x ∈ K_r(a) ⊓ P_r`. Each entry of `M - 1` is
  either an entry of `g - 1`, an entry of `x`, or zero. So
  `exists_mem_principalLevelSubgroup` gives an element of `K_r(a)` with the
  same matrix, and `Units.ext` identifies it with `M`. The last row of `M` is
  the last standard basis row, which is the mirabolic condition.
- `exists_of_unequalRankMatrix_eq` (support converse): let `0 < a`, let `u` be
  upper unipotent and `h ∈ K_r(a)`, and suppose
  `unequalRankMatrix j k g x = u * h`. Then some `c ∈ K_t(a)` has
  `g * c⁻¹ ∈ N_t`, and every entry of `x` lies in `levelSet F a`. Put
  `e = h⁻¹ ∈ K_r(a)`, so `M e = u`. Its leading `t × t` block is congruent
  to the identity, so `exists_mem_principalLevelSubgroup` makes it an element
  `E ∈ K_t(a)`. The leading rows of `M e = u` give `g E` equal to the leading
  block of `u`, which is upper unipotent; take `c = E⁻¹`. Row `t + p` of
  `M e = u`, in the first `t` columns, has zero on the right because `u` is
  upper triangular. It gives `(x E) p l = -e (t + p) l`. Hence
  `x = -e₂₁ E⁻¹`, where `e₂₁` is the rectangular block of `e`. Its entries
  lie in `𝔪^a` and those of `E⁻¹` are integral, so every entry of `x` lies in
  `levelSet F a`.

### Measure

- `isOpen_levelSet`: `levelSet F a` is open in `F`. The published
  `IsLocalRing.isOpen_maximalIdeal_pow` makes `𝔪^a` open in `O`, and `O` is
  open (`Valuation.isOpen_integer`), so the inclusion is an open map.
- `isCompact_levelSet`: `levelSet F a` is compact. An open additive subgroup
  of the compact ring `O` is closed, hence compact, and its image under the
  continuous inclusion is compact.

### Rectangular

- `entries_eq_pi` writes the set of matrices with all entries in `S` as the
  product set `Set.univ.pi (fun _ => Set.univ.pi (fun _ => S))`.
- `measurableSet_entries`: this set is measurable when `S` is.
- `rectangularMeasure_entries`: for `[SigmaFinite ν.measure]`,
  `rectangularMeasure ν j t {x | ∀ a b, x a b ∈ S} = (ν.measure S ^ t) ^ j`.
  The rectangular measure is by definition the nested finite product measure,
  so this is `Measure.pi_pi` twice. For `j = 0` the right side is `1`, which
  is the actual unit mass of the zero-row variable.

## The main proof

The proof installs `T.topology`, `T.valuativeRel` and `T.localField`, the Borel
structures and `BorelSpace` certificates exactly as in the statement, and the
published facts `T.fieldT2` and `T.sigmaCompactSpace` (from
`HarmonicAnalysis.PadicScalarHaarScalingProof`). Both are theorems about the
same supplied topology, so they add no hypothesis. The latter makes
`ν.measure` sigma-finite, as an additive Haar measure that is finite on
compacts.

1. *A fixed vector.* Since `ℓ'.val ≠ 0`, choose `w` with `ℓ'.val w ≠ 0`. The
   smoothness part of the admissibility clause of `IsOfWhittakerType` gives an
   open subgroup `K_w` of `GL_t` fixing `w`.
2. *One level for both ranks.* `Conductor.exists_pos_principalLevelOpenSubgroup_subset`
   gives `a₁ > 0` with `K_t(a₁)` inside `K_w` and inside the open kernel of
   `T.determinantNorm (n + 1)` (`TopologicalData.isOpen_ker_determinantNorm`).
   As in the published `Whittaker.mirabolicUnitTest` proof, the kernel of
   `χ = standardCharacter ψ r` is open in `N_r`. This uses
   `isOpen_ker_of_continuous_complex_character`, `standardCharacterContinuous`
   and `T.upperUnipotentNonarchimedean`. The induced topology then gives an
   identity neighbourhood `O_r` of `GL_(r+1)` whose preimage in `N_r` lies in
   `ker χ`. The same lemma gives `a₂` with `K_r(a₂) ⊆ O_r`. Let
   `a = max a₁ a₂ > 0`. By `Conductor.principalLevelSubgroup_antitone`, every
   `c ∈ K_t(a)` fixes `w` and has determinant norm one. Every `u ∈ N_r` in
   `K_r(a)` has `χ u = 1`.
3. *The larger test.* Let `H = K_r(a) ⊓ P_r` and
   `φ = MirabolicUnitTest.cosetExtension N_r H χ`. This is the published
   generic coset extension: `χ(u)` on `u H` and zero off `N_r H`. By
   `cosetExtension_left` it lies in `WhittakerFunctions ψ r`. The predicate
   `IsMirabolicTestFunction` comes from the published
   `isMirabolicTestFunction_of_compact_mirabolic_support`. It is applied with
   `K` the preimage of `K_r(a)` in `P_r` and `J = K_r(a)` as an open subgroup.
   `K` is compact as the preimage of the compact `K_r(a)`
   (`Conductor.isCompact_principalLevelOpenSubgroup`) under the closed
   embedding of the closed subgroup `P_r` (`GeneralLinear.Mirabolic.isClosed`).
   An element of `J` that lies in `P_r` is the image of an element of `K` by
   definition of the preimage. If `g ∉ N_r K`, then `g ∉ N_r H` because
   `H = K_r(a) ⊓ P_r` is the image of `K`, so `cosetExtension_eq_zero`
   gives `φ g = 0`. Right invariance under `K` is `cosetExtension_right`.
4. *Masses and the constant.* Let `Ω` be the published
   `compactOpenQuotientOrbit N_t K_t(a)`, the image of `K_t(a)` in the
   quotient. Let `X` be the matrices whose entries all lie in
   `levelSet F a`. `IsCompatible.compactOpenQuotientOrbit_mass` gives
   `0 < μ Ω < ∞` for the arbitrary compatible `μ`. `levelSet F a` is open,
   nonempty and compact, so it has positive finite `ν`-mass for the
   arbitrary `ν`. Then `rectangularMeasure_entries` gives `X` positive finite
   rectangular mass, equal to `1` when `j = 0`. Put
   `C = (μ.real Ω · rect.real X)⁻¹ ∈ ℂ`, where `rect` is
   `rectangularMeasure ν j (n + 1)`.
5. *The smaller vector.* `f' = (C · (ℓ'.val w)⁻¹) • modelMap σ ℓ' w`. It is an
   element of the actual coefficient model, and its value at `g` is
   `C · (ℓ'.val w)⁻¹ · ℓ'.val (σ g w)`. On `K_t(a)` it is the constant `C`,
   because `σ c w = w`. There the determinant weight is
   `|det c|^z = 1^z = 1` by `T.determinantNorm_coe` and `Complex.one_cpow`.
6. *The integrand is an indicator.* For every `s`, `x` and quotient point
   `q`, the integrand equals `C` times the indicator of `Ω ×ˢ X` at `(q, x)`.
   The quotient point is represented by `g`. If `q = [c]` with `c ∈ K_t(a)` and
   `x ∈ X`, then `M = unequalRankMatrix j k c x ∈ H` by block membership.
   So `cosetExtension_mul` with `u = 1` gives `φ M = 1`, and the integrand is
   `1 · C · 1`. Otherwise `φ M = 0`. If `M = u h` with `h ∈ H`, the support
   converse gives `c ∈ K_t(a)` with `g c⁻¹ ∈ N_t` and `x ∈ X`. Then
   `[g] = [c] ∈ Ω` by `QuotientGroup.rightRel_apply`, a contradiction.
   So `M ∉ N_r H`, and `cosetExtension_eq_zero` applies.
7. *Convergence.* A constant times the indicator of the measurable rectangle
   `Ω ×ˢ X` is integrable: `Measure.prod_prod_le` bounds its product mass by
   `μ Ω · rect X < ∞`. `Integrable.congr` transfers this to the integrand.
   This proves `UnequalRankConverges` for every `s`.
8. *The integral is one.* For fixed `q`, the inner rectangular integral is
   `rect.real X • C` when `q ∈ Ω` and `0` otherwise, by
   `integral_indicator_const`. Applying `integral_indicator_const` again on
   `Ω` gives `μ.real Ω • (rect.real X • C)`. By the choice of `C` this equals
   `1`, for every `s`. No Fubini theorem is needed, since the nested integral
   is computed pointwise.

## Comparison with the suggested route and the source

The task context suggests choosing a smaller coefficient normalized near the
identity and a small compact open subgroup of the larger mirabolic group. The
proof follows this route, with one concrete choice. Both ranks use principal
congruence subgroups of the same level `a`. With that choice, an explicit
Schur-complement computation describes the support exactly as `Ω × X`. The
witness `f'` is rescaled rather than `φ`, so `φ` takes the exact values of `χ`
on its support.

JPSS (H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983), 367–464,
source ID `jpss-1983-rankin-selberg`) is the source. Worker 856 read printed
pp.385–386 and 393–394 visually in the retained file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`
(SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`),
one-based PDF pages 20–21 and 28–29. No JPSS errata file was found among the
registered literature.

- §2.1 (pp.385–386) defines representations of Whittaker type and the spaces
  `𝒲(π; ψ)` of coefficient functions `g ↦ λ(π(g) v)`. The witness `f'` is such
  a coefficient for the specified functional, scaled by a constant.
- §2.2 (p.386) defines `𝒦₀(ψ)`: smooth functions on `P_r`, `θ`-covariant on
  the left under `N_r` and compactly supported modulo `N_r`. The restriction
  of `φ` to `P_r` is such a function. That is the content of
  `IsMirabolicTestFunction`.
- On p.393, in the equal-rank case, JPSS chooses `φ ∈ 𝒦₀(ψ)` and
  `φ' ∈ 𝒦₀(ψ̄)` so that the remaining integral is one. For `r > t` it states
  that nonvanishing of the block matrix value forces `x` into a compact set
  independent of `g`. On p.394 it asserts `I_j ∋ 1`, using
  `𝒦₀(ψ) ⊂ 𝒲(π; ψ)|P`.

JPSS gives no explicit construction of these functions and no computation of
the support. The level-`a` construction, the exact support description `Ω × X`
and the rescaling are internal to this proof. The proof establishes the
compact set on p.393 directly, for this test: the support converse puts `x`
in `X`. It does not prove the general compactness assertion of p.393, the
inclusion `𝒦₀(ψ) ⊂ 𝒲(π; ψ)|P` from [G-K], or any Kirillov lift. As the
statement prescribes, `φ` is a raw larger function, not lifted from a larger
representation.

## Downstream use

The theorem supplies the witnesses of the published compact-test interface.
A later proof can lift `φ` to a Whittaker model and use the result toward
`UnequalRankUnitSpanStatement`. This module proves neither that lift nor that
statement.

## Lean validation

All checks used `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The entry module compiled with zero
errors and warnings. Declaration inspection of
`Langlands.RankinSelberg.unequalRankMirabolicUnitTest` reported only
`propext`, `Classical.choice` and `Quot.sound` among its axioms.
