# Square integrability of cuspidal vectors on determinant bands via Siegel sets

Provenance: internal. This module proves that the vectors of a cuspidal
`OperatorRealization F n` are square integrable over one measurable set that meets the
rational orbit of every adelic matrix with determinant in a fixed band. It follows the
classical route to the square integrability of cusp forms: cover the rational orbits by a
Siegel set and use the rapid decay of cusp forms there. The Lean route is self-contained.
It uses the
Library's Siegel-set theorem
`PrimitiveAdelicHeight.exists_rational_mul_mem_siegelSetGL`, the block rapid-decay theorem
`OperatorRealization.exists_blockDecay` (module
`Langlands.Automorphic.CuspidalL2.Representation`) and the summation helper of
`Langlands.Automorphic.CuspidalL2.CompactCover`. It needs no finite-volume statement and no
central character.

Notation: `torInf F n x` is the archimedean torus element with entries `exp (x i)` at every
infinite place (module `Basics`), `A x := AdelicGL.ofInfinite F n (torInf F n x)`, and
`ev f := evaluate F n (S.toContinuous f)`.

## Elementary estimates on real vectors (namespace `Langlands.Automorphic.CuspidalL2`)

- `sub_le_of_adjacent x hB h`: if every step `x i - x j` with `j = i + 1` is at most
  `B ≥ 0`, then `x i - x j ≤ n * B` for all `i ≤ j`. Proof by induction on `j - i`.
- `Chamber K x` (definition): every consecutive increase `x j - x i` with `j = i + 1` is at
  most `K`.
- `sub_le_of_chamber hK hD x hx hdrop`: in a chamber, if all consecutive drops
  `x i - x (i + 1)` are at most `D ≥ 0`, then every difference `x i - x j` is at most
  `n * (K + D)`.
- `abs_le_of_sub_le x hT hR i`: if all differences are at most `T` and `|∑ x| ≤ R`, then
  `|x i| ≤ R + n * T`. Proof: `n x_i - ∑ x = ∑_j (x_i - x_j)`.
- `chamberDrop x a` (definition): the drop `x (a - 1) - x a` at a positive index, and `0`
  at the index `0`. `chamberDrop_of_succ` evaluates it at `j = i + 1`.
- `gap_le_of_chamber`: across a positive index `a`, every gap `x j - x i` with
  `i < a ≤ j` is at most `2 n K - chamberDrop x a`.
- `sum_abs_le_of_sub_le`: bounded differences and bounded sum give
  `∑ |x i| ≤ n * (R + n * T)`.
- `chamber_alternative hK x hx hR`: a chamber vector with `|∑ x| ≤ R` either satisfies
  `∑ |x i| ≤ B₀ := n (R + n (n (K + 2 n K)))`, or there are a positive index `a` and
  `ℓ ≥ 0` such that every gap `x j - x i` with `i < a ≤ j` is at most `-ℓ` and
  `∑ |x i| ≤ B₀ + n³ ℓ`. Proof: if every drop is at most `2 n K`, use the two previous
  bounds. Otherwise take `a` with maximal drop `D` (`Finset.exists_max_image`), so all
  drops are at most `D`. Set `ℓ := D - 2 n K`.
- `decay_exponent_le`: the real-number bookkeeping
  `-(N ℓ) + d (c₀ s) ≤ (c + d c₀) B₀ - c s` from `s ≤ B₀ + m ℓ`, `m (c + d c₀) ≤ N`,
  `0 ≤ ℓ` and `0 ≤ c + d c₀`.
- `summable_exp_neg_mul_abs_int hc`: `k ↦ exp (-(c |k|))` is summable on `ℤ` for `c > 0`.
  Both halves are geometric (`Summable.of_nat_of_neg`).
- `summable_prod_fin g hg hg0`: if `g : ℤ → ℝ` is nonnegative and summable, then
  `m ↦ ∏ i, g (m i)` is summable on `Fin n → ℤ`. Proof by induction on `n` through
  `Fin.consEquiv` and `Summable.mul_of_nonneg`.
- `floor_chamber x hx hR`: the integer parts `⌊x i⌋` form a vector in `Chamber (K + 1)`
  with `|∑ ⌊x i⌋| ≤ R + n`.
- `shift_chamber m y hy hm hR`: for `y` in the unit cube `[0, 1]^n`, a vector `m` in
  `Chamber (K + 1)` with `|∑ m| ≤ R + n` gives `m + y` in `Chamber (K + 2)` with
  `|∑ (m + y)| ≤ R + 2 n` and `∑ |m i| - n ≤ ∑ |(m + y) i|`.
- `summable_sq_lattice_bound P A`: for any predicate `P` on `Fin n → ℤ`, the function
  `m ↦ (A * exp (-(∑ |m i|)))²` is summable on the subtype `{m // P m}`. It is
  `A²` times the product of `exp (-(2 |m i|))`, restricted to the subtype
  (`Summable.comp_injective`).

## Heights, determinants and the torus (namespace `Langlands.Global`)

- `torInf_nsmul`: `torInf (k • y) = (torInf y)^k`. `matrixHeight_pow_succ_le`:
  `H (g^(k+1)) ≤ H(g)^(k+1)` for the Library's `ArchimedeanGL.matrixHeight`.
- `exists_matrixHeight_torInf_le`: there are `C₀, c₀ ≥ 0` with
  `H (torInf x) ≤ C₀ exp (c₀ ∑ |x i|)`. Proof: bound `H ∘ torInf` by `M₀ ≥ 1` on the
  compact cube `[-1, 1]^n`. Write `x = k • y` with `k = ⌈∑ |x i|⌉₊ + 1` and `y` in that cube,
  and use `H (g^k) ≤ H(g)^k`.
- `absDet F n g` (definition): the real number
  `((IdeleAbsoluteValue.full F (AdelicGL.determinant F n g) : ℝ≥0) : ℝ)`, the idelic
  absolute value of the determinant. It is definitionally the real coercion of
  `AdelicBlockDeterminantCharacter.determinantNorm F n g`. `absDet_mul`, `absDet_pos` and
  `continuous_absDet` say it is multiplicative, positive and continuous.
- `determinant_rational`: the determinant of a rational matrix is the diagonal idele of
  its rational determinant. `absDet_rational_mul`: left multiplication by a rational matrix
  preserves `absDet` (product formula `full_diagonalUnits`).
- `determinant_ofInfinite_torInf`: `det (A x) = PositiveRealIdeles.full F (expUnit (∑ x))`.
  `absDet_ofInfinite_torInf`: `absDet (A x) = exp (∑ x) ^ finrank ℚ F`.
- `realScale F s` (definition): the adele with the real scalar `s` at every infinite place
  and finite part `1`. `realScale_mul`, `realScale_zero_mul` and `continuous_realScale`
  give its multiplicativity, a zero-product rewrite and its continuity.
- `torInf_neg`, `ofInfinite_torInf_val`: `A x` has matrix `diagonal (realScale (exp (x i)))`.
  `ofInfinite_torInf_conj_apply`: the `(i, j)` entry of `(A x)⁻¹ M (A x)` is
  `realScale (exp (x j - x i)) * M i j`.
- `continuous_diagonalGL`: the Library's `PrimitiveAdelicHeight.diagonalGL` is continuous
  on `Fin n → Ideles F`.
- `conj_apply_mem`: for `x` in `Chamber K` and an upper triangular `M` with entries in
  `E₀`, every entry of `(A x)⁻¹ M (A x)` lies in the image of
  `[0, exp (n K)] × E₀` under `(s, w) ↦ realScale s * w`. Entries below the diagonal are
  `0`.
- `exists_siegelDecomposition`: there are a compact `Q₁ ⊆ AdelicGL F n` and `K ≥ 0` such
  that every `g` has `γ`, `x` and `q ∈ Q₁` with `rational γ * g = A x * q` and `x` in
  `Chamber K`. Proof: the Siegel-set theorem writes `rational γ * g = N · ω · A x · κ`.
  Here `N` is unitriangular in a compact set, `ω` is diagonal with entries in a compact set
  of norm-one ideles, `κ` lies in `standardCompact`, and the torus satisfies
  `|r_j| ≤ c |r_i|` for `j = i + 1`. Taking logarithms gives the chamber condition with
  `K = max 0 (log c / finrank ℚ F)`. Then `rational γ * g = A x · ((A x)⁻¹ N (A x)) · ω · κ`.
  The conjugated `N` and its inverse (conjugated `adjugate N`) have entries in a fixed
  compact set by `conj_apply_mem`. So `Q₁` is the product of the Library's compact
  `AdelicMatrixHeight.entryBox`, the compact image of the diagonal entries, and
  `standardCompact`.
- `adelicGL_t2Space`: `AdelicGL F n` is Hausdorff, from the Hausdorff property of the
  infinite and finite adele rings.
- `abs_sum_le_of_absDet x q`:
  `|∑ x| ≤ |log absDet (A x * q)| + |log absDet q|`. This uses
  `log absDet (A x * q) = finrank · ∑ x + log absDet q` and `finrank ℚ F ≥ 1`.

## Decay and the band cover (namespace `Langlands.Automorphic.OperatorRealization`)

- `exists_torus_growth f Q hQ`: there are `d` and `C` with
  `‖ev f (A x * q)‖ ≤ C · H (torInf x)^d` for all `x` and `q ∈ Q`. This is the enveloping
  degree-zero case (`map_one`) of `exists_uniform_growth`.
- `exists_chamber_decay [CompactSpace (AdeleQuotient F)] hS f Q hQ hK hc`: for a cuspidal
  realization, a compact `Q`, `K ≥ 0`, any `R` and `c ≥ 0`, there is `C` with
  `‖ev f (A x * q)‖ ≤ C · exp (-(c ∑ |x i|))` whenever `x` is in `Chamber K`,
  `|∑ x| ≤ R` and `q ∈ Q`. Proof by `chamber_alternative`. In the bounded regime, the
  growth bound and `exists_matrixHeight_torInf_le` give a constant. In the other regime, use
  `exists_blockDecay` for the block `(a, n - a)` with
  `N = ⌈n³ (c + d₂ c₀)⌉₊` and gap `ℓ`, together with the height bound. Then
  `decay_exponent_le` turns `exp (-N ℓ) · exp (d₂ c₀ ∑ |x i|)` into a constant times
  `exp (-(c ∑ |x i|))`. The constants of the finitely many blocks are summed.
- `norm_le_on_lattice_translate`: given such a decay bound for `Chamber (K + 2)` and sums
  at most `R + 2 n`, a vector `m` in `Chamber (K + 1)` with `|∑ m| ≤ R + n`, `y` in the unit
  cube and `q ∈ Q₁` satisfy
  `‖ev f (A m * (A y * q))‖ ≤ |C| · exp n · exp (-(∑ |m i|))`. This uses `shift_chamber` and
  `A m * A y = A (m + y)`.
- `exists_band_cover [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
  [CompactSpace (AdeleQuotient F)] hS hlo`: for a cuspidal operator realization `S` and
  real numbers `0 < lo` and `hi`, there is a set `t ⊆ AdelicGL F n` with three properties.
  1. `t` is measurable.
  2. Every `g` with `lo ≤ absDet F n g ≤ hi` has a rational `γ` with `rational γ * g ∈ t`.
  3. For every left-invariant measure `μ` that is finite on compact sets and every
     `f : S.Space`, `∫⁻ x in t, ‖ev f x‖ₑ ^ 2 ∂μ < ⊤`.

  Construction:
  - Let `Q₁`, `K` come from `exists_siegelDecomposition`, and let `L` bound
    `|log absDet|` on `Q₁`.
  - Set `R₀ := max |log lo| |log hi| + L`.
  - Let `Q₂` be the compact image of `[0, 1]^n × Q₁` under `(y, q) ↦ A y * q`.
  - Let `ι` be the integer vectors in `Chamber (K + 1)` with `|∑ m| ≤ R₀ + n`, and set
    `t := leftTranslateCover (fun m : ι => A m) Q₂`.

  Proof of the three properties:
  1. Measurability: `measurableSet_leftTranslateCover`.
  2. Covering: decompose `rational γ * g = A x * q`. Then `abs_sum_le_of_absDet` and
     `absDet_rational_mul` give `|∑ x| ≤ R₀`. Write `x = ⌊x⌋ + fract x` (`floor_chamber`),
     so `rational γ * g = A ⌊x⌋ * (A (fract x) * q)`.
  3. Integrability: `exists_chamber_decay` with `K + 2`, `R₀ + 2 n` and `c = 1`, followed by
     `norm_le_on_lattice_translate`, bounds `ev f` on the translate `A m · Q₂` by
     `|C| · exp n · exp (-(∑ |m i|))`. These bounds have summable squares
     (`summable_sq_lattice_bound`), and `lintegral_enorm_sq_leftTranslateCover_lt_top`
     gives finiteness.

  The `CompactSpace (AdeleQuotient F)` hypothesis is needed only because
  `OperatorRealization.IsCuspidal` is stated under it. The Library proves it as
  `Langlands.Global.compactSpace_adeleQuotient`.
