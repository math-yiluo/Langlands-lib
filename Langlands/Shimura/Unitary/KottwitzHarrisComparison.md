# Kottwitz's polynomial for Harris's signature, through the base-change parameters

Module `Langlands.Shimura.Unitary.KottwitzHarrisComparison`, namespace
`Langlands.Shimura.KottwitzDual`.

This module is item 5 of Task 5424. It covers the Shimura data used by Harris
(1999) and Clozel (1991): signature `(n − 1, 1)` at one real place `τ₀` of the
totally real field and `(n, 0)` at the others. For these data it proves an
identity that expresses Kottwitz's polynomial `P(π_p, E_v)` (item 3, module
`KottwitzPolynomial`) through the unramified base-change parameters `BC(π)_w`
(item 4, module `KottwitzBaseChange`) at the place `w` of the CM field defined
by `θ ∘ Φ τ₀`:

```
P(π_p, E_v) = ∏_{β ∈ BC(π)_w} (X − α · β^{f / f_w}).
```

Here:

- `f = localDegree p θ nfun` is the local degree of the reflex field at `v`;
- `f_w = inertiaDegree w` is the inertia degree of `w`;
- `α` is a single scalar that does not depend on `β`. It is described below.

The identity is a theorem about the Library's objects. It is proved in Lean
for every normalized lift `t̂` of every principal-series character `ξ`. It
assumes `n ≥ 3` and two hypotheses on Frobenius orbits at `Φ τ₀`, `hper` and
`horb` (see "Hypotheses"). The results are:

- `kottwitzPolynomialOf_harris`: a product over the positions `j`;
- `kottwitzPolynomialOf_harris_baseChangeParameter`: a product over the
  multiset `BC(π)_w`;
- `kottwitzPolynomialOf_harrisCharts`: the same, for the Library's Harris datum
  `HarrisSignatureCharts`;
- `localDegree_eq_inertiaDegree_harris` and
  `kottwitzPolynomialOf_harris_baseChangeParameter_of_preserves`: under one
  more hypothesis `hR`, `f = f_w` and the exponent is `1` (see "The exponent
  `f / f_w` and the reflex field").

In general `f / f_w` need not be `1`. By Clozel, the reflex field is the
compositum of the distinguished image of the CM field with the reflex field of
the CM type.

It builds on the published modules `KottwitzRepresentation`,
`KottwitzPolynomial`, `KottwitzDualTorus`, `KottwitzLiftIndependence`,
`KottwitzPrincipalSeries`, `KottwitzBaseChange` and `Reflex`, and imports them
by Lean name.

## Conventions

The conventions are those of `KottwitzPolynomial.md`:

- `E` is the totally real field (Kottwitz's `F₀`) and `K` the CM field
  (Kottwitz's `F`).
- `S = (E →+* ℝ)`, and `Φ` is a CM type (`IsCMSection E K Φ`).
- `nfun : (K →+* ℂ) → ℕ` is Kottwitz's function `i ↦ n(i)`, with
  `n(i) + n(ī) = n` (`hconj`). It is read on the CM indices `S × Bool` as
  `h = cmHodge hΦ nfun`, with `h(τ, true) = n(Φ τ)` and
  `h(τ, false) = n(conj Φ τ)`.
- `k_τ = h(τ, false) = hodgeDegrees h τ`.
- `W = ⨂_τ ⋀^{k_τ} Lⁿ` is the space of Kottwitz's representation `r`. On
  `(ζ, (g_τ)) ∈ Ĝ`, `r` acts by `ζ⁻¹ ⊗ ⨂_τ det(g_τ)⁻¹ ⋀^{k_τ} g_τ`
  (`dualRep`).
- `kottwitzBasis` is the standard basis `⨂_τ e_{T_τ}` of `W`, indexed by
  families `T` of subsets `T_τ ⊂ {0, …, n − 1}` with `|T_τ| = k_τ`.
- A dual-torus point is `t = (ζ, (s_{τ,k})) ∈ Ωˣ × (S → Fin n → Ωˣ)`.
  `cocharPairing t a = ζ^{a₀} ∏ s_{τ,k}^{a_{τ,k}}` is its pairing with a
  cocharacter `a = (a₀, (a_{τ,k}))`.
- `G` is a CM permutation (in the application `frobeniusCMPerm hΦ θ`).
  `normCochar n G f a = Σ_{r < f} cocharPullback n (G^r) a` is the norm, dual
  to `N_f` on `T̂`: `⟨t, N(a)⟩ = ⟨N_f(t), a⟩` (`cocharPairing_torusNorm`).
- `posCochar τ j` is the coordinate cocharacter `e_{τ,j}`: multiplier `0`,
  `1` at `(τ, j)` and `0` elsewhere.
- `s` is the chosen square root of `p` (`SqrtPrime`). `kottwitzFrobenius` is
  `V(Φ_v) = s^{f · dim S} · r(N_f(t̂) ⋊ Φ_v)`, and `kottwitzCharpoly` is its
  characteristic polynomial.

Harris's signature is the hypothesis pair `h0 : k_{τ₀} = 1` and
`hτ0 : k_τ ∈ {0, n}` for `τ ≠ τ₀`. In terms of `nfun`, it reads
`n(conj Φ τ₀) = 1` and `n(conj Φ τ) ∈ {0, n}` for `τ ≠ τ₀`. The Library's Harris
datum has `k_τ = 0` for `τ ≠ τ₀` (see the last section). The case `k_τ = n` is
the same signature with `Φ τ` and its conjugate exchanged, and is allowed.

## The torus acts diagonally on the standard basis (section `Weights`)

- `map_diagonal_ιMulti_basisFun`: `⋀^k(diag d)` multiplies
  `e_{g(0)} ∧ ⋯ ∧ e_{g(k−1)}` by `∏_j d_{g(j)}`.
- `exteriorPower_basisFun_apply`: the basis vector `e_U` of `⋀^k Lⁿ` is the
  wedge of the elements of `U` in increasing order. `prod_orderEmbOfFin`: a
  product over this enumeration is the product over `U`.
- `wedgeRep_diagUnit_basis`: `det(g)⁻¹ ⋀^k g` for `g = diag(s_j)` acts on
  `e_U` by `∏_{j ∉ U} s_j⁻¹`.
- `basisWeight T` is the weight `(−1, (τ, j) ↦ 0 if j ∈ T_τ, −1 otherwise)` of
  the basis vector `⨂_τ e_{T_τ}`.
- `dualRep_torusElement_basis`: `r(t̂)(⨂_τ e_{T_τ}) = ⟨t, basisWeight T⟩ ·
  ⨂_τ e_{T_τ}`.

## Frobenius on the standard basis (section `Frobenius`)

- `exteriorPower_basisFun_eq_hwVector`: in `⋀⁰ Lⁿ` and `⋀ⁿ Lⁿ`, the unique
  standard basis vector is the highest-weight vector `hwVector` used by
  `frobOp`. `exteriorPower_basisFun_coe_congr` transports basis vectors along
  an equality of indices.
- `frobOp_kottwitzBasis`: suppose `k_τ ∈ {0, n}` for `τ ≠ τ₀`, and the CM
  permutation `G` preserves `h` and fixes `(τ₀, true)`. Then `r(1 ⋊ G)` fixes
  every standard basis vector. Proof: `G` fixes the factor `τ₀` and does not
  cross there. At the other factors, `⋀^{k_τ}` is a line spanned by
  `hwVector`, and `factorEquiv_hwVector` applies.
- `kottwitzFrobenius_torusElement_basis`: if moreover `G^f` fixes `(τ₀, true)`,
  then `V(Φ_v)` acts on `⨂_τ e_{T_τ}` by the scalar
  `s^{f · dim} · ⟨t, N(basisWeight T)⟩`.
- `toMatrix_eq_diagonal` and `charpoly_toMatrix_eq_prod` are general linear
  algebra. An operator that is diagonal in a basis has a diagonal matrix there,
  and its characteristic polynomial is `∏_i (X − d_i)`.
- `kottwitzCharpoly_torusElement`: under the same hypotheses,
  `P = ∏_T (X − s^{f · dim} ⟨t, N(basisWeight T)⟩)`, the product taken over
  all standard basis vectors.

## The pairing with `2ρ` (section `TwoRho`)

`twoRhoPairing a = Σ_{τ,k} (n − 1 − 2k) a_{τ,k}` is `⟨2ρ, a⟩`.

- `rho_coeff_rev` and `sum_rho_coeff`: `n − 1 − 2 rev(k) = −(n − 1 − 2k)`, and
  `Σ_k (n − 1 − 2k) = 0`.
- `twoRhoPairing_cocharPullback`: `⟨2ρ, ·⟩` is invariant under every
  `cocharPullback`. At a crossing the coordinates become `a₀ − a_{τ, rev k}`;
  the `a₀` term contributes `a₀ Σ_k (n − 1 − 2k) = 0`, and reversing `k`
  changes the sign of the coefficient.
- `twoRhoPairing_sum` (additivity) and `twoRhoPairing_normCochar`:
  `⟨2ρ, N(a)⟩ = f ⟨2ρ, a⟩`. `normCochar_add`: the norm is additive.
- `twoRhoPairing_posCochar`: `⟨2ρ, e_{τ₀,j}⟩ = n − 1 − 2j`.

## Reduction to one index at `τ₀` (section `Harris`)

Assume `h0` and `hτ0`.

- `card_harris`, `harrisIndex`, `harrisIndex_spec`: `T_{τ₀}` is a singleton
  `{j(T)}`.
- `mem_harris_ne`: for `τ ≠ τ₀`, `T_τ` is empty if `k_τ = 0` and everything if
  `k_τ = n`.
- `harrisBaseWeight h τ₀` is the weight `a₀` common to all basis vectors.
  Its multiplier exponent is `−1`. Its coordinate `(τ, i)` is `−1` if
  `τ = τ₀` or `k_τ = 0`, and `0` otherwise.
- `basisWeight_eq_harris`: `basisWeight T = a₀ + e_{τ₀, j(T)}`.
- `harrisIndex_injective` and `harrisIndex_bijective`: `T ↦ j(T)` is a
  bijection from the standard basis onto `{0, …, n − 1}`. So `dim r = n`.
- `kottwitzCharpoly_harris`: if moreover `G^f` fixes `(τ₀, true)`, then

  ```
  P = ∏_{j < n} (X − s^{f · dim} ⟨t, N(a₀)⟩ ⟨t, N(e_{τ₀,j})⟩).
  ```

## Counting returns to a periodic point (section `Orbits`)

Elementary counting lemmas:

- `sum_range_mul_of_periodic`: for `g` periodic with period `P`,
  `Σ_{r < N P} g(r) = N Σ_{r < P} g(r)`.
- `sum_range_ite_dvd_add`: for `P > 0`, exactly one `r < P` has
  `P ∣ r + r₀`.
- `sum_range_ite_pow_apply_eq`: let `x₀` have minimal period `P > 0` under a
  permutation `F`. Then `#{r < N P : F^r x = x₀}` is `N` if `x` lies in the
  forward orbit of `x₀`, and `0` otherwise.

## The norm of a position cocharacter (section `PositionNorm`)

- `cocharPullback_posCochar_snd`: the coordinate `(τ, k)` of the pullback of
  `e_{τ₀,j}` along `G` is `[G(τ, true) = (τ₀, true) ∧ k = j] −
  [G(τ, true) = (τ₀, false) ∧ rev k = j]`.
- `normCochar_posCochar_fst` and `normCochar_posCochar_snd`: the norm
  `N(e_{τ₀,j})` has multiplier `0`, and coordinate `(τ, k)` equal to the sum of
  these brackets over `G^r`, `r < f`.

## Frobenius orbits and places above `p` (section `Places`)

Here `F = frobeniusPerm K p θ` is the Frobenius permutation of the complex
embeddings of `K`, and `w(i) = harrisPlace p θ i` is the place of `K` above `p`
defined by `θ ∘ i`. The proof uses the following helpers:

- The private `pow_apply_conjugate_aux`: powers of `F` commute with complex conjugation.
- The imported `harrisPlace_conjugate` from `KottwitzFrobeniusPlaces`: `w(ī) = w̄`.

The public declarations are:

- `sum_range_frobeniusPerm_pow_eq`: let `F^f` fix `i₀`, and assume `hper` and
  `horb` at `i₀`. Then `#{r < f : F^r i = i₀}` equals `f / f_w` if
  `w(i) = w(i₀)`, and `0` otherwise.
- `frobeniusCMPerm_pow_apply_eq_iff`: `G^r` sends the CM index `x` to `y`
  exactly when `F^r` sends the embedding of `x` to the embedding of `y`.
- `frobeniusPerm_pow_localDegree_harris`: let `n ≥ 3`, `n(conj Φ τ₀) = 1`, and
  `n(conj Φ τ) ∈ {0, n}` for `τ ≠ τ₀`. Then `F^f` fixes `Φ τ₀`, for
  `f = localDegree p θ nfun`. Proof: `F^f` preserves `nfun`
  (`hodgeOrbitDegree_preserves`). Since `n − 1 ≥ 2` and `n ≥ 3`, `conj Φ τ₀` is
  the only embedding where `nfun` takes the value `1`. So `F^f` fixes
  `conj Φ τ₀`, hence also `Φ τ₀`. For `n = 2` the values at `Φ τ₀` and its
  conjugate are both `1`, and this argument fails. Clozel uses `n > 2` in the
  same way (printed p.134): an automorphism fixing the signature function must
  fix `ι₀`.
- `normCochar_posCochar_eq_embeddingCochar`: let `F^f` fix `Φ τ₀` with `f > 0`,
  and assume `hper` and `horb` at `Φ τ₀`. Then, with `w = w(Φ τ₀)`,

  ```
  N(e_{τ₀,j}) = embeddingCochar θ Φ ((f / f_w) • λ_{w,j}),
  ```

  where `λ_{w,j} = positionCocharacter E p n w j` is item 4's position
  cocharacter. Its coordinates are `+1` at `(w, j)` and `−1` at
  `(w̄, rev j)`. Proof: by `normCochar_posCochar_snd`, the coordinate `(τ, k)`
  of the norm counts the `r < f` with `F^r Φ τ = Φ τ₀` (when `k = j`), minus
  those with `F^r Φ τ = conj Φ τ₀` (when `rev k = j`). By the counting lemma
  and `w(ī) = w̄`, these counts are `f / f_w` exactly when `w(Φ τ) = w`,
  resp. `w(Φ τ) = w̄`. These are the coordinates of
  `embeddingCochar((f / f_w) λ_{w,j})`.
- `cocharPairing_normCochar_posCochar_harris`: let `t̂` be a normalized lift
  (`IsNormalizedLift c θ s ξ t`) of a character `ξ` of the chart's torus. Then,
  under the same hypotheses,

  ```
  ⟨t, N(e_{τ₀,j})⟩ = β_j^{f / f_w},   β_j = c.positionValue s ξ w j.
  ```

  Here `β_j = ξ(λ_{w,j}(p)) · s^{f_w (n − 1 − 2j)}` is item 4's unitarily
  normalized position value. Proof: by the previous identity and the
  normalization, the pairing is `ξ(λ_{w,j}(p))^{f/f_w} · s^{⟨2ρ, N(e_{τ₀,j})⟩}`.
  By the `TwoRho` section, `⟨2ρ, N(e_{τ₀,j})⟩ = f (n − 1 − 2j)`. Here `f_w`
  divides `f` (`hper`, with `F^f Φ τ₀ = Φ τ₀`), so this exponent is
  `(f / f_w) · f_w (n − 1 − 2j)`.

### Main results

- `kottwitzPolynomialOf_harris`: assume `n ≥ 3`, `hconj`,
  `h0 : n(conj Φ τ₀) = 1`, `hτ0 : n(conj Φ τ) ∈ {0, n}` for `τ ≠ τ₀`, and
  `hper`, `horb` at `Φ τ₀`. Then, for every normalized lift `t̂` of
  `(s, ξ)`,

  ```
  kottwitzPolynomialOf θ hΦ nfun hconj s t
    = ∏_{j < n} (X − α · β_j^{f / f_w}),
  α = s^{f · dim} · ⟨t, N(harrisBaseWeight)⟩,   β_j = c.positionValue s ξ w j,
  ```

  where `w = harrisPlace p θ (Φ τ₀)`, `f = localDegree p θ nfun`,
  `f_w = inertiaDegree w` and `dim = hodgeDim (cmHodge hΦ nfun)`. The proof
  combines `frobeniusPerm_pow_localDegree_harris` (which gives `hfix`),
  `kottwitzCharpoly_harris` and `cocharPairing_normCochar_posCochar_harris`.
- `kottwitzPolynomialOf_harris_baseChangeParameter`: the same polynomial is
  `∏_{β ∈ BC(π)_w} (X − α · β^{f / f_w})`, the product over the multiset
  `c.baseChangeParameter s ξ w` of item 4. That multiset is `symOfFn` of the
  position values.

Consequently, if `ξ` is a principal-series parameter of `π_p`, every
polynomial in the relation `IsKottwitzPolynomialOver` (item 3) obtained from
`ξ` has the above form, with `BC(π)_w` the base-change parameter of item 4
(`IsBaseChangeParameterOf`). The relations themselves are defined in items 3
and 4 and are not restated here.

### Hypotheses

- `hper : minimalPeriod F (Φ τ₀) = f_w` and
  `horb : ∀ j, w(j) = w(Φ τ₀) ↔ ∃ r, F^r (Φ τ₀) = j`. Together they say that
  the Frobenius orbit of `Φ τ₀` is the set of embeddings inducing `w`, and that
  it has `f_w` elements. They are the two conjuncts at `i = Φ τ₀` of
  `FrobeniusOrbitsArePlaces K p θ`, which is defined in the Library module
  `KottwitzFrobeniusPlaces`. That module defines the Prop but does not prove
  it. Mathematically the statement holds when `K_w/ℚ_p` is unramified, as it
  is at Kottwitz's good primes; that module's Markdown explains why. Here the
  two conjuncts are explicit hypotheses and are not proved.
- `n ≥ 3` is Clozel's assumption `n > 2` (§5, printed p.134). It is used only
  to prove that `F^f` fixes `Φ τ₀`. Together with `hper`, this gives only
  that `f_w` divides `f`.
- `hR` (only in `localDegree_eq_inertiaDegree_harris` and
  `kottwitzPolynomialOf_harris_baseChangeParameter_of_preserves`): every power
  `F^r` that fixes `Φ τ₀` preserves `nfun`. See the next section.
- No imaginary quadratic subfield of `K` is needed. The identity holds for
  every CM type `Φ`, and in particular for Harris's `harrisCMSection`.

## The exponent `f / f_w` and the reflex field

Clozel describes the reflex field of this datum in §5. On printed p.131 he
fixes a CM type `S` of `F_c` and lets `R` be the reflex field of `(F_c, S)`:
the subfield of `ℚ̄ ⊂ ℂ` generated by the partial traces `Σ_{ι ∈ S} ι(x)`,
`x ∈ F_c`. `R` is a CM field. Definition 5.2 (p.131) sets `E = F_c R`, and
notes that `E = F_c` when `F_c` (or `F`) is Galois over `ℚ`. On p.134 Clozel
justifies this. An element `σ` of `Gal(ℚ̄/ℚ)` fixes his signature function
exactly when `σ ι₀ = ι₀` (this step uses `n > 2`) and `σ S = S`. So the
reflex field is the compositum `E = (ι₀ F_c) R`. In general `R` need not lie
in `ι₀ F_c`, and then `E` is strictly larger than `ι₀ F_c`.

In the Lean statements, `f = localDegree p θ nfun` is the least `r > 0` such
that `F^r` preserves `nfun`. By `hper`, `f_w` is the length of the Frobenius
orbit of `Φ τ₀`. `frobeniusPerm_pow_localDegree_harris` formalizes the
`σ ι₀ = ι₀` half of Clozel's argument: `F^f` fixes `Φ τ₀`, so `f_w` divides
`f`. Preservation of `S` is not used. `f` can be larger than `f_w`, so the
general theorems keep the exponent `f / f_w`. At a good prime, `E_v/ℚ_p` and
`K_w/ℚ_p` are unramified. Then `f = [E_v : ℚ_p]` (an identification documented
in `KottwitzDualGroup.md`, not proved) and `f_w = [K_w : ℚ_p]`. So
`f / f_w = [E_v : ℚ_p] / [K_w : ℚ_p]`. This ratio is `1` when `E = ι₀ F_c`,
and can be larger otherwise.

The exponent is `1` under an additional hypothesis:

- `localDegree_eq_inertiaDegree_harris`: assume `n ≥ 3`, `hconj`, `h0`,
  `hτ0`, `hper` and

  ```
  hR : ∀ r, F^r (Φ τ₀) = Φ τ₀ → ∀ i, n(F^r i) = n(i).
  ```

  Then `localDegree p θ nfun = inertiaDegree w`, that is `f = f_w`. Proof:
  `F^{f_w}` fixes `Φ τ₀` (`iterate_minimalPeriod` and `hper`), so by `hR` it
  preserves `nfun`. Minimality of `f` (`Nat.find_min'`) gives `f ≤ f_w`.
  Conversely `F^f` fixes `Φ τ₀`, so `f_w ∣ f` with `f > 0`.
- `kottwitzPolynomialOf_harris_baseChangeParameter_of_preserves`: under the
  hypotheses of `kottwitzPolynomialOf_harris_baseChangeParameter` and `hR`,

  ```
  kottwitzPolynomialOf θ hΦ nfun hconj s t = ∏_{β ∈ BC(π)_w} (X − α · β),
  ```

  with the same scalar `α`. The proof rewrites `f / f_w = 1` in the general
  identity.

`hR` is the Frobenius form of the condition `R ⊂ ι₀ F_c`. In Lean it is a
hypothesis. The following justification is not formalized.

- Dictionary. `nfun` corresponds to Clozel's signature function `p`, with
  `ι₀ = conj Φ τ₀` (the only embedding where `nfun` takes the value `1`).
  Clozel's CM type is `S = {conj Φ τ₀} ∪ {i : n(i) = n}`.
- By `KottwitzDualGroup.md`, `F(i) = θ⁻¹ ∘ Frob ∘ θ ∘ i`. Restricted to `ℚ̄`,
  this is `F(i) = φ ∘ i` for an element `φ` of `Gal(ℚ̄/ℚ)`.
- Suppose `F^r` fixes `Φ τ₀`. Then `F^r` also fixes `conj Φ τ₀ = ι₀`, because
  `F` commutes with complex conjugation (`frobeniusPerm_conjugate`). So `φ^r`
  fixes the field `ι₀ F_c` pointwise.
- If `R ⊂ ι₀ F_c`, then `φ^r` fixes `R`, the fixed field of the stabilizer of
  `S`, so `φ^r S = S`. By the converse step on Clozel's p.134, an element that
  fixes `ι₀` and preserves `S` fixes `p`. So `F^r` preserves `nfun`.

The condition `R ⊂ ι₀ F_c` holds for instance when `K` is Galois over `ℚ`. Then
all embeddings of `F_c` have image `ι₀ F_c`, so `ι₀ F_c` contains the partial
traces that generate `R`. This is Clozel's remark `E = F_c` after
Definition 5.2. Without such a condition `hR` can fail, and the general theorem
with `f / f_w` applies.

## The Library's Harris datum

`H : HarrisSignatureCharts σ n Φ` (module `HarrisLevels`) is the Library's
datum of Harris's signature: `(n − 1, 1)` at the distinguished real place
`τ₁ = H.distinguished`, and `(n, 0)` elsewhere. Kottwitz's function of this
datum is `H.hodgeFunction` (module `Reflex`).

- `harrisCharts_hodgeFunction_section`: `n(Φ τ)` is `n − 1` if `τ = τ₁`, and
  `n` otherwise.
- `harrisCharts_hodgeFunction_conjugate_section`: `n(conj Φ τ)` is `1` if
  `τ = τ₁`, and `0` otherwise.
- `harrisCharts_hodgeFunction_add_conjugate`: `n(i) + n(ī) = n`. This uses
  `n > 1` (`H.rank_gt_one`).
- `kottwitzPolynomialOf_harrisCharts`: assume `n ≥ 3`, and `hper` and `horb`
  at `Φ τ₁`. Then Kottwitz's polynomial of `H.hodgeFunction` is
  `∏_{β ∈ BC(π)_w} (X − α · β^{f / f_w})`, with `w = harrisPlace p θ (Φ τ₁)`.
  The hypotheses `hconj`, `h0` and `hτ0` are discharged by the three lemmas
  above.

## Comparison with the sources

- **Kottwitz (1992), §1, printed pp.656-657.** `V(π_p, E_v) =
  (r ∘ φ_{E_v}(π_p)) ⊗ χ`, and `P(π_p, E_v)` is the characteristic polynomial
  of `Φ_v` on it. The objects `kottwitzFrobenius` and `kottwitzPolynomialOf`
  are item 3's formalization of these, and this module computes them.
- **Clozel (1991), §5, (5.24)-(5.31), printed pp.140-141.** Clozel computes
  the image of Frobenius under the parameter in the same situation. Formula
  (5.26) gives the diagonal element `(t_{π_c,u}, …, t_{π_c,u}; β_u(ϖ_u))` of
  `GL(n, ℂ)^d × ℂˣ`. Its image (5.27)-(5.28) under the map (5.10) (printed
  p.136: `r ∘ φ` at Frobenius, with Kottwitz's twist, whose characteristic
  polynomial is `P`) is `t^{−1}_{π_c,u} ω_{c,u}(ϖ_u)^{−(d−1)} β_u(ϖ_u)^{−1}`, which equals (5.29)
  up to permutation, by self-duality. After restriction to `W_{E_w}`, (5.31)
  writes the Frobenius matrix as `r^T(𝓕_w) q_w^{(n−1)/2} α_{E,w}(ϖ_w)`, with
  `α_E` an Artin character. Our identity has the same shape: every eigenvalue
  is one scalar `α` times a unitarily normalized base-change Satake parameter.
  The power `β^{f/f_w}` is the restriction from `W_{K_w}` to `W_{E_v}`, the
  analogue of Clozel's passage from `𝓕_u` to `𝓕_w`. The inverse in (5.27)
  corresponds to the choice of place. At the conjugate place `w̄`, item 4
  gives the inverse parameters (`baseChangeParameter_placeConj`:
  `BC(π)_{w̄} = BC(π)_w^{−1}`, with `f_{w̄} = f_w`). So the identity can be
  read either with `BC(π)_w` or with the inverses of `BC(π)_{w̄}`. This
  rewriting is not formalized here.
- **Harris (1999), Theorem 5.7(ii), printed p.313.** At almost all unramified
  places `w`, the normalized local `L`-function of `ρ(π)` at `w` is the
  standard Euler factor `L(s, BC_{𝒦/E}(π)_w)`. The identity above is the local
  statement behind this: up to the scalar `α`, the eigenvalues of geometric
  Frobenius on Kottwitz's `V` are the base-change Satake parameters at `w`
  (raised to the power `f/f_w`).

## What is not claimed

- `α` is not identified with Clozel's `q_w^{(n−1)/2} α_{E,w}(ϖ_w)`, nor with a
  value of the similitude or central character of `π`. Here `α` is the explicit
  pairing `s^{f · dim} ⟨t, N(a₀)⟩`. It is the same for all eigenvalues. By the
  definition of `harrisBaseWeight`, it involves only the multiplier coordinate
  and full determinants at the factors `τ₀` and `k_τ = 0`. The module does not
  prove that it is independent of the lift `t̂`.
- `f = f_w` without further hypotheses. It can fail, because the reflex field
  `E = (ι₀ F_c) R` (Clozel, printed pp.131 and 134) can be larger than `ι₀ F_c`.
  It is proved only under the extra hypothesis `hR`
  (`localDegree_eq_inertiaDegree_harris`). The relation between `R ⊂ ι₀ F_c`
  and `hR` is explained above but not formalized.
- `hper` and `horb` are hypotheses (see above).
- No global statement is made. Nothing here concerns Galois representations,
  `L`-functions, the cohomology of Shimura varieties, or the global base-change
  theorems of Clozel or Harris–Labesse. Existence and uniqueness of
  principal-series parameters (Satake) are neither assumed nor proved.

## Sources

- R. E. Kottwitz, *On the λ-adic representations associated to some simple
  Shimura varieties*, Invent. Math. 108 (1992), §1, printed pp.656-657
  (`kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`):
  `V(π_p, E_v)`, the twist `(√p)^{[E_v:ℚ_p] dim S_K}` and `P(π_p, E_v)`.
- L. Clozel, *Représentations galoisiennes associées aux représentations
  automorphes autoduales de GL(n)*, Publ. Math. IHÉS 73 (1991), §5
  (`clozel-1991-selfdual-galois`, SHA-256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`; PDF page
  = printed page − 95). Printed p.131: the CM type `S`, its reflex field `R`,
  and Definition 5.2, `E = F_c R` (`E = F_c` if `F_c` or `F` is Galois over
  `ℚ`). Printed p.134: the signature function (`1` at `ι₀`, `n − 1` at `c ι₀`,
  `n` on `S − {ι₀}`, `0` on `c(S − {ι₀})`). An automorphism fixes it exactly
  when it fixes `ι₀` (this direction uses `n > 2`) and preserves `S`. Hence the
  reflex field is the compositum `E = (ι₀ F_c) R`. Printed p.136,
  (5.9)-(5.10): Kottwitz's representation `r` and `P` as the characteristic
  polynomial of (5.10). Printed pp.140-141, (5.24)-(5.31): the image of
  Frobenius and its shape `r^T(𝓕_w) q_w^{(n−1)/2} α_{E,w}(ϖ_w)`.
- M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39 (1999), Theorem 5.7(ii), printed p.313, PDF p.15
  (`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`): the
  local factor at `w` is `L(s, BC_{𝒦/E}(π)_w)`.

Provenance. The statement is derived. Kottwitz's `V` and `P` and item 4's
base-change parameters are the source objects. The identity is the explicit
form, in the Library's coordinates, of the computation (5.24)-(5.31) of
Clozel. The Lean proof is internal: diagonalization in the standard basis,
counting Frobenius returns, and the `2ρ` invariance. It is described above.
