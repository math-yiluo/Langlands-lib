# Proof: partial Euler factorization of the equal-rank dual global Whittaker integral

Module `Langlands.Global.RankinSelberg.EqualDualEulerFactorizationProof`.

The theorem `Langlands.Global.RankinSelbergGlobal.equalDualEulerFactorization` proves the
Library statement
`Langlands.Global.RankinSelbergGlobal.EqualDualEulerFactorizationStatement.{u, uQ}` (module
`Langlands.Global.RankinSelberg.EqualDualEulerFactorizationStatement`). The statement is
unchanged. Both universe parameters stay free: `u` for the number field and `uQ` for the
local factors of the spectral presentations. The only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

The proof is direct. It does not use the Library's conditional reduction
`EqualDualEulerFactorizationReduction`, whose premise `ContragredientDualWhittakerStatement`
is still open. It follows `equalEulerFactorization_of_gauge` (module
`EqualEulerFactorizationReduction`) line by line, with the dual functions `W̃`, `W̃'`, `Φ̂` in
place of `W`, `W'`, `Φ`. It needs three changes:

1. integrability comes from the dual gauge estimate;
2. the splitting of `W̃`, `W̃'` at an unramified place comes from
   `ContragredientDualSplit.dualWhittaker_split`;
3. `Φ̂` is standard outside `S` by `fourierStandardOutside`.

Unless stated otherwise, every module named below is in `Langlands.Global.RankinSelberg`.

## Notation

`n = r + 1`. `W̃ = dualFunction F n (cuspWhittaker F T ψ x)` and
`W̃' = dualFunction F n (cuspWhittaker F T' ψ⁻¹ x')` (here `ψ` stands for `ψ.complex`).
`Φ̂ = fourierTransform F n ψ Φ`. Further notation:

- `f_Φ(s)` is `equalWhittakerIntegrand F W̃ W̃' Φ s`, a function on
  `N_n(𝔸) \ GL_n(𝔸)`;
- `ι_v(h)` is `localPoint F n v h`, and `g_v` is `finiteComponent F n v g`;
- `ϖ_v` is `placeUniformizer v`, and `ϖ_v^λ` is `torus ϖ_v λ`;
- `U_A` is `unipotentIntegralClasses F n A`: the classes whose representative has
  `g_w ∈ N_n(F_w) GL_n(𝒪_w)` at every finite `w ∉ A`;
- `sphInv v ψ_v r a` and `sphStd v ψ_v r b` (module `UnequalDualEulerFactorizationReduction`)
  are the spherical Whittaker functions `W°⁻(·; a)` and `W°(·; b)` of `GL_n(F_v)`, for the
  inverse standard and the standard character of `ψ_v`.

## Auxiliary lemmas (namespace `Langlands.Global.RankinSelbergGlobal.EqualDualEuler`)

- `dualIntegrand_mk`. For every `g`,
  `f_Φ(s)(N_n(𝔸) g) = W̃(g) W̃'(g) Φ(e_n g) |det g|^s`. The integrand is defined through a
  representative `u g` of the class. `Unfolding.dualCuspWhittaker_unipotent_mul` (module
  `UnfoldingDual`) says that `W̃` transforms under `N_n(𝔸)` by the generic character of `ψ⁻¹`
  and `W̃'` by that of `ψ`. With `Unfolding.genericCharacter_inv_eq_inv` the two characters
  cancel. `e_n (u g) = e_n g` and `|det (u g)| = |det g|`.
- `dualWhittaker_mul_localPoint_torus`. Assume `v ∉ S`, that `ψ_v` is the canonical component
  of `ψ` at `v` with additive conductor `0`, that `a` and `b` enumerate the spectra of `Pd` and
  `Pd'` at `v`, and that `g_v ∈ N_n(F_v) GL_n(𝒪_v)`. Then
  `W̃(ι_v(ϖ_v^λ) g) W̃'(ι_v(ϖ_v^λ) g) = c_a(λ) c_b(λ) · W̃(g) W̃'(g)`. Here
  `c_a(λ) = δ^(1/2)(ϖ_v^λ) s_λ(a)` for antitone `λ` and `0` otherwise (`halfModulus`,
  `satakeSchur`). Proof: write `g = g' ι_v(g_v)` with `g'_v = 1`
  (`finiteComponent_mul_inv_localPoint`). Then `ι_v(ϖ_v^λ) g = g' ι_v(ϖ_v^λ g_v)`
  (`localPoint_mul_eq`). `dualWhittaker_split` (first half for `T`, `Td`, `Pd`; second half
  for `T'`, `Td'`, `Pd'`) gives `W̃(g' ι_v(h)) = W̃(g') W°⁻(h; a)` and
  `W̃'(g' ι_v(h)) = W̃'(g') W°(h; b)`. The inverse standard and the standard character are
  mutually inverse. So `LocalPointFactorization.sphericalWhittaker_mul_sphericalWhittaker`
  evaluates `W°⁻(h; a) W°(h; b)` as `c_a(λ) c_b(λ)` at `h = ϖ_v^λ g_v`, whose Iwasawa
  exponent is `λ`. The companion lemma `..._of_exponent_eq_zero` gives `1` at `h = g_v`,
  whose exponent is `0`. The residue cardinality is rewritten to `N(v)` by
  `EqualEulerPointwise.residueCardinality_canonical`.
- `dualIntegrand_localPoint_torus_mul`. Under the same hypotheses, and with `Φ` standard
  outside `S`, the product `W̃ W̃' Φ(e_n ·) |det ·|^s` at `ι_v(ϖ_v^λ) g` is
  `cellMultiplier N(v) a b s λ` times its value at `g`. The Whittaker part is the lemma
  above. The Schwartz part is `EqualEulerSchwartz.apply_lastRow_localPoint_torus`: the
  factor is `1` if `λ_n ≥ 0` and `0` otherwise. The determinant part is
  `detPower_localPoint_mul` with `log_norm_det_torus`. The resulting power of `N(v)` is
  identified with `spectralPoint N(v) s ^ (∑ λ_i)` by
  `EqualEulerLocal.exp_mul_log_zpow_eq_spectralPoint_pow`.
- `integrand_shift`. For a finite `A`, `v ∉ A` with `v ∉ S`, and `q ∈ U_A`:
  `f_Φ(s)(N_n(𝔸) ι_v(ϖ_v^λ) q.out) = cellMultiplier N(v) a b s λ · f_Φ(s)(q)`. This
  combines `dualIntegrand_mk` (twice) with the previous lemma at `g = q.out`.
- `setIntegral_insert` (the one-place step). Assume `f_Φ(s)` is integrable,
  `HasSatakeBound Pd C`, `HasSatakeBound Pd' C'`, `Φ` standard outside `S`, and
  `EqualEulerLocal.localRadius r C C' < Re s`. Let `v ∉ S` and `v ∉ A`. Then
  `∫_(U_(A ∪ {v})) f_Φ(s) = partialEulerFactor Pd Pd' hPd hPd' v s · ∫_(U_A) f_Φ(s)`.
  The proof:
  - `FiniteAdditiveSupport ψ S` gives the local component `ψ_v` with conductor `0`.
  - `Unramified.Eigenvalues.ofTuple_surjective` gives tuples `a`, `b` enumerating the
    spectra of `Pd`, `Pd'` at `v`.
  - `whittakerCellDecomposition` writes `∫_(U_(A ∪ {v})) f_Φ(s)` as the unconditional sum
    over `λ ∈ ℤ^n` of `N(v)^(modulusExponent λ) ∫_(U_A) f_Φ(s)(ι_v(ϖ_v^λ) ·)`.
  - By `integrand_shift` and
    `EqualEulerPointwise.zpow_modulusExponent_mul_cellMultiplier`, the term at `λ` is
    `equalRankLocalTerm a b (spectralPoint N(v) s) λ · ∫_(U_A) f_Φ(s)`.
  - `EqualEulerLocal.hasSum_equalRankLocalTerm_eulerFactor` sums these terms to the pair
    Euler factor `(P_(A,B)(N(v)^(-s)))⁻¹ = partialEulerFactor Pd Pd' hPd hPd' v s`. The
    bounds needed are the Satake bounds at `v`, with
    `CuspidalPairEulerConvergence.residueCardinality_eq_absNorm` and
    `two_le_residueCardinality`.
  - The two sums are equal by uniqueness of sums.

## The main proof

Let the data of the statement be given. Set `hstd := isStandardAdditiveCharacter_of_unitary`.

- `integrable_dualEqualWhittakerIntegrand_of_gauge` (module `EqualUnfoldingReduction`) is
  applied to the dual gauge premise
  `equalGaugeDualSpecialization whittakerSchwartzGauge F r T T'` (modules
  `EqualGaugeDualSpecialization`, `WhittakerSchwartzGauge`). It gives `C₀` such that for
  `C₀ < Re s` the integrand `f_Φ̂(s)` of `W̃`, `W̃'`, `Φ̂` is integrable for
  `whittakerQuotientMeasure`, for every `Φ ∈ schwartzBruhat F n`. This is the first
  conclusion.
- `exists_partialEulerFactor_convergence Pd Pd' hPd hPd'` (module
  `PartialEulerProductConvergence`) gives `σ₂`. For `σ₂ < Re s`, `∑_v ‖L̃_v(s) − 1‖`
  converges and `∏_v L̃_v(s)` has the value `partialEulerProduct Pd Pd' hPd hPd' s`. These
  are the second conclusion and the product `p`.
- `exists_hasSatakeBound_presentation` applied to `Td`, `Pd` and to `Td'`, `Pd'` gives the
  Satake bounds `C`, `C'`.
- The chosen threshold is `σ = max C₀ (max σ₂ (localRadius r C C'))`.
- `fourierStandardOutside F ψ S hψS n Φ hΦ` (module `FourierStandardOutsideProof`) shows
  that `Φ̂` is standard outside `S`.
- `partialEqualWhittakerIntegral_eq_setIntegral` turns the partial integral into
  `∫_(U_S) f_Φ̂(s)`. `integral_eq_hasProd_mul_setIntegral` (module
  `PartialIntegralExhaustion`) then gives
  `∫ f_Φ̂(s) = p · ∫_(U_S) f_Φ̂(s)`. Its one-place hypothesis is `setIntegral_insert` with
  `Φ̂` in place of `Φ`. Commuting the product gives the identity in the statement.

## Provenance and route

The statement Markdown cites Cogdell 2004 (`cogdell-2004-analytic-theory-gln`, PDF page =
printed page + 3) for the following facts:

- §2.2, printed p.207: `W̃(g) = W(w_n ᵗg⁻¹)`;
- §2.3, pp.210–211: the factorization of the global integral and the unfolding of the
  dual side;
- Theorem 3.3, p.215: the unramified computation;
- §4.1, pp.219–220: the partial L-function `L^S(s, π̃ × π̃')` on the dual side.

Cogdell gets the dual unramified local integral from Theorem 3.3 applied to the
contragredient pair, with `W̃` the Whittaker function of `φ̃`, a form in `π̃`. In the Library
that route needs a vector of `Td` whose Whittaker function is `W̃`. This is the open
`ContragredientDualWhittakerStatement`, which rests on multiplicity one and on the
transpose-inverse realization of the contragredient. The Lean proof avoids this step.
`ContragredientDualSplit.dualWhittaker_split` gets the splitting of `W̃` at `v ∉ S` from the
Hecke action of `T` and local duality of spherical Whittaker functions, without any vector
of `Td`. The Satake parameters of `π̃_v`, `π̃'_v` enter only through the presentations
`Pd`, `Pd'`. The local unramified sum is then evaluated exactly as in the primal case:
the cell decomposition, the products of spherical Whittaker values, and the local sum of
module `EqualEulerLocalSum`, all done one place at a time. Cogdell states the convergence
without proof. Here it comes from the Library's dual Whittaker–Schwartz gauge estimate. The
assembly is internal to the Library.
