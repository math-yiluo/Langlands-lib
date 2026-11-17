# Rank-one realizations with a real-place parameter

Helper module for the rank-one (`r = 0`) case of
`Langlands.Global.RankinSelbergGlobal.RealEqualFunctionalEquationStatement`. Authored by
Worker 823. Every declaration is proved; there are no hypotheses beyond those stated in
each declaration and no axioms are added.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealRankZero`. The module builds on
`RealRankZeroPlace` (Schur scalars, `minusOneOrthogonal`, `scalarUnit`,
`realPlaceAdelic`, `evaluate_mul_realPlaceAdelic`, `cuspWhittaker_rankZero`).

## The character `χ_c ∘ det` of `GL₁(ℝ)`

Section `Character`. `c : RealCharacterData` has parity `e ∈ Fin 2`, exponent `t ∈ ℂ` and
character `χ_c(x) = sgn(x)^e |x|^t` of `ℝˣ`.

- `characterFunction c : GL₁(ℝ) → ℂ` is `g ↦ χ_c(det g)`.
  `characterFunction_mul` and `characterFunction_one`: it is multiplicative and sends `1`
  to `1`.
- `character_exp`: `χ_c(eᵘ) = exp(t u)`. `character_neg_one`: `χ_c(-1) = (-1)^e`.
- `rightTranslation_characterFunction`: right translation by `h` (the Library's
  `Whittaker.rightTranslation`) multiplies `χ_c ∘ det` by `χ_c(det h)`.
- `determinant_val_fin_one`: the determinant of `g ∈ GL₁(ℝ)` is its entry.
- `contMDiff_characterFunction`: `χ_c ∘ det` is smooth on the manifold `GL₁(ℝ)`. On
  invertible matrices `Y` it agrees with `Y ↦ sgn(Y₀₀)^e |Y₀₀|^t`, which is smooth near
  every `Y` with `Y₀₀ ≠ 0` (Library lemmas `PrincipalSeriesExtension.contDiff_entry` and
  `contDiffAt_ofReal_cpow`).
- `characterFunction_mem_principalSeries`: `χ_c ∘ det` lies in the Library's principal
  series `principalSeries ℝ 1 (realPositionCharacter [character c])`: it is smooth, and
  `f(a u g) = χ_c(a) f(g)` for diagonal `a` and upper unitriangular `u` (in rank one `u = 1`
  has determinant `1` and `det a = a₀`).
- `characterFunction_mem_realStandardModule`: it lies in the Library's real standard
  module `realStandardModule 1 [character c]`. The extra condition there concerns
  two-dimensional blocks, which do not occur in `[character c]`.
- `characterFunction_mem_kFinite`: it lies in the `O(1)`-finite part
  `realStandardKFinite 1 [character c]`. Its compact translates are scalar multiples of
  itself, so they span a space of dimension at most one.
- `rightDerivative_characterFunction`: the Library's right derivative of `χ_c ∘ det`
  along `1 ∈ 𝔤𝔩₁(ℝ)` is `t · (χ_c ∘ det)`. The right derivative is the derivative at `0` of
  `u ↦ f(g · eᵘ)` (via the Library's `rightDerivative_eq_fderiv_mul_left` and the chain
  rule along `u ↦ eᵘ · 1`), and `f(g · eᵘ) = f(g) exp(t u)` by `character_exp`.

## Linear-algebra lemmas

- `eq_of_smul_eq_smul`: in a complex vector space, `a • x = b • x` with `x ≠ 0` gives
  `a = b`.
- `bilinear_smul_smul`, `bilinear_smul_left`, `bilinear_smul_right`:
  `B(a x, b y) = a b B(x, y)`, `B(a x, y) = a B(x, y)`, `B(x, b y) = b B(x, y)` for a
  complex bilinear form `B`. The module instances are implicit arguments, read off from
  `B`.
- `eq_one_of_mul_eq_self`: `p z = z` with `z ≠ 0` gives `p = 1`.

## The Schur scalars of a realization with a rank-one real parameter

Section `Realization`. `F` is a number field, `v` a real place and
`S : OperatorRealization F 1`. The Library's
`S.HasRealPlaceParameter v [character c]` provides an injective linear map
`A : realStandardKFinite 1 [character c] → S.Space` that intertwines the right `O(1)`
translations with `S.realPlaceCompactRepresentation v` and the right derivatives with
`S.realPlaceLieAction v`.

- `parameter_characterFunction_ne_zero`: `A(χ_c ∘ det) ≠ 0`, because `A` is injective
  and `χ_c ∘ det` takes the value `1` at `1`.
- `hasRealPlaceParameter_nontrivial`: such an `S` has a nonzero vector.
- `hasRealPlaceParameter_compact`: if `S` is irreducible and has the parameter
  `[character c]` at `v`, then `-1 ∈ O(1)` at `v` acts on `S.Space` by `χ_c(-1)`. By
  `exists_compactRepresentation_eq_smul` it acts by some scalar `ε`. Applying the
  intertwining property to `χ_c ∘ det` gives `χ_c(-1) A(f₀) = ε A(f₀)` for the nonzero
  vector `A(f₀)`, so `ε = χ_c(-1)`.
- `exists_realPlaceLieAction_eq_smul`: if `S` is irreducible, the Lie operator of every
  `X ∈ ℂ ⊗ 𝔤𝔩₁(ℝ)` at `v` is a scalar. It is the enveloping action of a generator
  (`realPlaceLieAction_apply`), which is a scalar by `exists_envelopingAction_eq_smul`.
- `hasRealPlaceParameter_lie`: if `S` is irreducible and has the parameter
  `[character c]` at `v`, then the Lie operator of `1 ∈ 𝔤𝔩₁(ℝ)` at `v` acts by `t`. The
  argument is the one for `hasRealPlaceParameter_compact`, with
  `rightDerivative_characterFunction` in place of `rightTranslation_characterFunction`.

The two Lie lemmas raise the heartbeat limit to `1000000` for elaboration.

### Contragredients

The Library's `IsContragredientOf Sd S` provides a bilinear pairing
`B : S.Space × Sd.Space → ℂ` that is invariant under the compact group and under which the
Lie operators are skew, and for which `B.flip` is injective.

- `exists_pairing_ne_zero`: for `y ≠ 0` in `Sd.Space` some `x` has `B(x, y) ≠ 0`.
- `contragredient_parity_rankOne`: let `S` and `Sd` be irreducible, `Sd` a
  contragredient of `S`, and let them have parameters `[character c]` and
  `[character cd]` at `v`. Then `cd` and `c` have the same parity. Compact invariance at
  `-1` gives `χ_c(-1) χ_cd(-1) B(x, y) = B(x, y)` with `B(x, y) ≠ 0`, so
  `(-1)^e (-1)^{ed} = 1`, which forces equal parities in `Fin 2`.
- `contragredient_exponent_rankOne`: under the same hypotheses
  `cd.exponent = -c.exponent`. Skewness of the Lie operator of `1` gives
  `t B(x, y) + td B(x, y) = 0` with `B(x, y) ≠ 0`.

## Global Whittaker restrictions of cuspidal realizations of `GL₁`

Section `Whittaker`, with `[CompactSpace (AdeleQuotient F)]` (an assumption of the
Library's `cuspWhittaker`).

- the existing `RealPlaceWhittaker.cuspFunction_eq_evaluate`: the Library's `cuspFunction F T x` at a point `z` is the
  realized continuous function `T.realization.toContinuous x` at the adelic matrix of
  `z`.
- `realPlaceAdelic_apply`: unfolding of `realPlaceAdelic`.
- `adelicEquiv_realPlacePoint_mul_finitePoint`: the adelic matrix of
  `realPlacePoint v g * finitePoint a` is `(1, a) · ι_v(g)`.
- `isRealPlaceWhittaker_rankZero`: let `T : CuspidalOperatorRealization F 0`, `χ` an
  additive character of the adeles, and `W` a real-place Whittaker restriction in the
  Library's sense (`IsRealPlaceWhittaker F T χ v W`: `W(g)` is the global Whittaker
  coefficient of some `x` at `realPlacePoint v g * finitePoint a`). If `-1 ∈ O(1)` acts by
  `χ_c(-1)` and the Lie operator of `1` by `t`, then `W = C · χ_c ∘ det` for a constant `C`.
  By `cuspWhittaker_rankZero` the Whittaker coefficient is the cusp function itself; by the
  two previous lemmas `W(g)` is the realized function at `(1, a) · ι_v(g)`; and
  `evaluate_mul_realPlaceAdelic` gives `W(g) = χ_c(det g) · C` with `C` the realized
  function at `(1, a)`.

## Provenance

The function `χ ∘ det` spans the rank-one principal series of `GL₁(ℝ)`; its
`O(1)`-type and its derivative determine the character. The contragredient of a
character is its inverse. These are standard. Their formalization against the Library's
`HasRealPlaceParameter`, `IsContragredientOf` and `IsRealPlaceWhittaker` interfaces is
internal to this project.
