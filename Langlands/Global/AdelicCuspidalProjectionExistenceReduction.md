# Automorphic cuspidal projections from continuous ones

Module `Langlands.Global.AdelicCuspidalProjectionExistenceReduction` proves

```lean
theorem Langlands.Global.cuspidalProjectionExistenceReduction :
    CuspidalProjectionExistenceReductionStatement.{u}
```

where `CuspidalProjectionExistenceReductionStatement` (module
`Langlands.Global.AdelicCuspidalProjectionExistenceReductionStatement`) is the implication

```
LeviCuspFormPairingMajorantStatement → ParabolicCuspidalVanishingStatement →
  ParabolicReproducingKernelStatement → ContinuousCuspidalProjectionExistenceStatement →
    CuspidalProjectionExistenceStatement
```

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It proves the
implication, not its premises.

## The argument

Fix the data of `CuspidalProjectionExistenceStatement` and an automorphic `φ` on
`U_Q(𝔸) M_Q(F) \ G(𝔸)`. `ContinuousCuspidalProjectionExistenceStatement` gives a continuous
cuspidal projection `ψ₀`: continuous, of moderate growth, left invariant under
`U_Q(𝔸) M_Q(F)`, cuspidal along `Q`, and with integrable Levi pairing integrands whose integrals
agree with those of `φ` against every Levi cusp form at every point.

**Size zero.** If the matrix embedding has size `0`, the closed embedding of `G(𝔸)` into
`GL_0(𝔸)` makes `G(𝔸)` a single point. Then `ψ₀` is constant, and
`isAutomorphicFunctionOn_of_subsingleton` shows that it is automorphic: it is continuous, its
archimedean slices are constant and hence plot-smooth, every open subgroup fixes it, its
translates span a space of dimension at most one, and its slices lie in the finite-dimensional
space of plot-smooth functions on a one-point group, so an ideal of finite codimension of the
centre annihilates them (`exists_cofiniteIdeal_annihilates_of_finite_centralOrbit`). So `ψ₀` is
the required projection.

**Positive size.** `ParabolicReproducingKernelStatement` gives a smooth compactly supported
test function `α` with finite-dimensional span of left `K_∞`-translates and
`rightConvolution F G α φ = φ`. The projection is `ψ = rightConvolution F G α ψ₀`,
`ψ(g) = ∫ α(a) ψ₀(g a) da`. Both `φ` and `ψ₀` have polynomial growth in the adelic height
(`hasModerateGrowthFunction_iff_hasHeightGrowth`), with nonnegative exponents.

1. *Pairings of convolutions.* For every continuous compactly supported kernel `k`, every
   Levi cusp form `t` and every `g`, the pairing integrand of `k * ψ₀` is integrable and
   `(( k * ψ₀)(·g), t) = ((k * φ)(·g), t)`. Both sides are given by
   `leviPairing_rightConvolution` as `∫ k(y) (f(·gy), t) dy` for `f = ψ₀` and `f = φ`, with the
   majorants of `LeviCuspFormPairingMajorantStatement` at the growth exponents of `ψ₀` and of
   `φ`; the inner pairings agree pointwise because `ψ₀` is a continuous projection of `φ`.
2. *Regularity of convolutions.* For every test kernel `k`, `k * ψ₀` is left invariant
   (`isLeftInvariantUnder_rightConvolution`), continuous and indeed smooth with a finite level
   (`adelicRightConvolutionDifferentiation`), of moderate growth with the exponent of `ψ₀`
   (`norm_rightConvolution_le_of_height_bound`), and cuspidal along `Q`
   (`isCuspidalAlong_rightConvolution`).
3. *Uniqueness.* If a test kernel `k` satisfies `k * φ = 0`, then `k * ψ₀ = 0`: by steps 1 and 2,
   `k * ψ₀` is a continuous cuspidal function of moderate growth whose pairings all vanish, and
   `eq_zero_of_inCuspidalAnnihilator` applies the vanishing criterion
   `ParabolicCuspidalVanishingStatement` to it.
4. *Automorphy of `ψ`.* Left invariance, smoothness and moderate growth come from step 2.
   `K_∞`-finiteness comes from the left `K_∞`-finiteness of `α`: converted by
   `isInfiniteSubgroupFiniteFunction_inv_of_leftFinite` to the hypothesis of the published
   `isInfiniteSubgroupFiniteFunction_rightConvolution`. Centre finiteness comes from
   `isCenterFiniteFunction_rightConvolution_of_reproducing`, with the annihilating ideal of `φ`
   and the uniqueness of step 3.
5. *Cuspidality and pairings of `ψ`.* Cuspidality is step 2 for `k = α`. Integrability of the
   pairing integrand of `φ` is part of the continuous projection; that of `ψ` and the equality
   `(ψ(·g), t) = ((α * φ)(·g), t) = (φ(·g), t)` are step 1 for `k = α` and
   `rightConvolution F G α φ = φ`.

## Auxiliary declarations

Namespace `Langlands.Global.AdelicGroupPoints`:

- `subgroupConstantTerm_rightConvolution_apply_of_rationalImage`: for a closed subgroup
  `j : U → G` with compact rational quotient, a continuous compactly supported kernel `h` and a
  continuous `f` invariant under the rational points of `U` on the left, the constant term along
  `U` of `h * f` is `h` convolved with the constant term of `f`. The proof is Fubini's theorem on
  the compact quotient times `G(𝔸)` (`integral_integral_swap_of_hasCompactSupport`), as in the
  Library's `subgroupConstantTerm_rightConvolution_apply`, which assumes invariance under all of
  `G(F)`.
- `isInfiniteSubgroupFiniteFunction_inv_of_leftFinite`: if the left translates `h ↦ α(k h)`,
  `k ∈ K_∞`, span a finite-dimensional space, then `g ↦ α(g⁻¹)` is right `K_∞`-finite; the
  span of its translates is contained in the image of the first span under `ψ ↦ ψ(·⁻¹)`.
- `isCenterFiniteFunction_rightConvolution_of_reproducing`: let `α` be a test kernel with
  `α * φ = φ` for a continuous `φ` annihilated by an ideal `J` of finite codimension of the centre
  `𝔷`, and let `ψ₀` be continuous with `k * ψ₀ = 0` whenever `k * φ = 0` for a test kernel `k`.
  Then `J` annihilates `α * ψ₀`. For `z ∈ J`, the published `adelicRightConvolutionEnveloping`
  gives one test kernel `α_z` with `z (α * f) = α_z * f` on every archimedean slice, for every
  measurable locally integrable `f`. Applied to `φ`, the left side is `z` applied to the slices
  of `φ`, which vanishes, so `α_z * φ = 0`; hence `α_z * ψ₀ = 0`, and this is `z` applied to the
  slices of `α * ψ₀`.

Namespace `Langlands.Global.StandardParabolicFamily`:

- `heightScale F N`: the constant `N^{∑_v m_v}` with
  `adelicHeight = heightScale F N · adelicSourceNorm`
  (`RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm`), and `heightScale_nonneg`.
- `leviRational_mul_of_parabolicInvariant`: left invariance under `U_Q(𝔸) M_Q(F)` gives left
  invariance under the image of `M_Q(F)`.
- `leviPairingIntegrand_mk`: the Levi pairing integrand of a function invariant under the
  rational Levi, against a test invariant under `M_Q(F)`, is `f(ι(m) g) \overline{t(m)}` at the
  class of any norm-one `m`.
- `continuous_leviPairingIntegrand_uncurry`, `continuous_leviPairingIntegrand`: for continuous
  `f` and `t`, the integrand is continuous on the norm-one quotient, jointly in the class and in a
  right translation parameter, since the quotient map times the identity is an open quotient map.
- `norm_leviPairingIntegrand_mk_le`: if `|f| ≤ C · ht^r` with `r ≥ 0` (`ht = adelicHeight`), then
  the integrand of the translate by `g y` at the class of `x` is at most
  `C · heightScale^r · ht(y)^r · ‖ι(x) g‖^r |t(x)|`, by submultiplicativity of the height.
- `integrable_leviPairingIntegrand_of_majorant`: such an `f` has an integrable pairing integrand
  against any test with a weighted majorant (`HasLeviPairingMajorant`) at the exponent `r`.
- `leviPairing_rightConvolution`: for such an `f`, a continuous compactly supported kernel `h`
  and a test with a weighted majorant at `g`, the pairing integrand of `h * f` is integrable and
  `(( h * f)(·g), t) = ∫ h(y) (f(·g y), t) dy`. The integrand
  `(q, y) ↦ h(y) (f(·g y) \overline t)(q)` is continuous and bounded by a constant times the
  product of the majorant in `q` and of `|h(y)| ht(y)^r` in `y`, so it is integrable on the
  product of the norm-one quotient (of finite volume, `connectedReductiveFiniteVolume`) with
  `G(𝔸)`. The pairing integrand of `h * f` is its integral in `y`, and Fubini's theorem
  (`integral_integral_swap`) exchanges the integrals.
- `rationalRadicalImage_le_parabolicQuotient`: for standard `R ≤ P`, the rational points of the
  radical `U_R` lie in `U_P(𝔸) M_P(F)`.
- `isCuspidalAlong_rightConvolution`: compact right convolution preserves cuspidality along `P`
  of continuous functions on `U_P(𝔸) M_P(F) \ G(𝔸)`, by the constant-term identity above.
- `isIwasawaCompact_of_minimal` in `AdelicLeadingCuspidalInjectivityReduction`: a compact with `P₀(𝔸) K = G(𝔸)` satisfies `P_R(𝔸) K = G(𝔸)`
  for every standard `R`.
- `eq_zero_of_inCuspidalAnnihilator`: for a positive-size embedding, a continuous cuspidal function
  of moderate growth on `U_Q(𝔸) M_Q(F) \ G(𝔸)` in the fibrewise cuspidal annihilator of `Q` is
  zero. Its constant term along `Q` is itself (`constantTerm_eq_self_of_unipotent_invariant`),
  its constant terms along smaller standard parabolics vanish, and
  `ParabolicCuspidalVanishingStatement` applies.

Namespace `Langlands.Global`:

- `isAutomorphicFunctionOn_of_subsingleton`, described under *Size zero* above.

## Provenance

The cuspidal projection of Mœglin–Waldspurger I.2.18 (pp. 39–40) is constructed automorphic
directly, for a fixed central character, by duality between finite-dimensional spaces of cusp
forms, and Bernstein–Lapid (6.8) characterizes it by the fibrewise pairings used here. The
argument above instead deduces automorphy from a continuous projection. It is a fibrewise
adaptation of the proof of the converse in the Lemma of Mœglin–Waldspurger I.3.5 (p. 48), which
convolves a function of moderate growth with a kernel from I.2.17 reproducing its cuspidal
components and uses the vanishing criterion I.3.4 both to show that the convolution does not
change the function and to obtain its finiteness under the centre. Here the kernel is
Harish-Chandra's reproducing kernel for `φ` (Mœglin–Waldspurger I.2.17, Lemma; Harish-Chandra,
*Discrete series for semisimple Lie groups II*, §8, Theorem 1), the pairings are those of
Bernstein–Lapid (6.8), and the zero test is the Library's vanishing criterion
`ParabolicCuspidalVanishingStatement` (Mœglin–Waldspurger I.3.4; Bernstein–Lapid (8.1)). The
analytic estimates are the Library's weighted majorants of Levi cusp forms (Mœglin–Waldspurger
I.2.12, I.2.18) and its convolution and differentiation theorems for adelic test functions.
