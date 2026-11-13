# Frobenius, conjugation and the places above `p` of a CM field

Module `Langlands.Shimura.Unitary.KottwitzFrobeniusPlaces`, namespace
`Langlands.Shimura.KottwitzDual`.

This module adds to items 2–3 of Task 5424. It works with Kottwitz's polynomial
`P(π_p, E_v)` (modules `KottwitzPolynomial`, `KottwitzLiftIndependence`). The
results of `KottwitzLiftIndependence` assume two hypotheses on the embedding
`θ : ℂ →+* Q̄_p` and the CM section `Φ`:

- `Function.Injective (embeddingCochar θ Φ)`;
- `FrobeniusInvariantsRational E K n p θ hΦ`.

Those results are: the polynomial does not depend on the lift `t̂`, and lifts
exist. This module proves the first hypothesis outright
(`embeddingCochar_injective`). It reduces the second to a single statement about
embeddings, `FrobeniusOrbitsArePlaces K p θ`: the orbits of geometric Frobenius on
the complex embeddings of `K` are the fibres of the place map, and the orbit of
`i` has as many elements as the inertia degree of its place.

Notation: `K` is a number field (a CM field `K ⊇ E` in the second half),
`p` a prime, `θ : ℂ →+* Q̄_p` a ring homomorphism (`Q̄_p = PadicAlgCl p`).
`harrisPlace p θ i` is the place of `K` above `p` cut out by `θ ∘ i`. This is the
prime of algebraic integers `x` with `|θ(i(x))|_p < 1` (Library module
`HarrisCMTypePlaces`). `frobeniusPerm K p θ` is the permutation
`i ↦ θ⁻¹ ∘ Frob ∘ θ ∘ i` of the complex embeddings. Here `Frob` is the Library's
geometric Frobenius `geometricFrobenius p ∈ Gal(Q̄_p/ℚ_p)` (module
`KottwitzDualGroup`).

## Definitions

- `FrobeniusOrbitsArePlaces K p θ : Prop` holds when, for every complex embedding
  `i : K →+* ℂ`, both of the following hold:
  - `Function.minimalPeriod (frobeniusPerm K p θ) i = inertiaDegree (harrisPlace p θ i)`,
    so the Frobenius orbit of `i` has `f_w` elements, where `w` is the place of
    `i` and `f_w = [k_w : 𝔽_p]`;
  - for every `j`, `harrisPlace p θ j = harrisPlace p θ i` if and only if
    `j = Frob^r ∘ i` for some `r : ℕ`.

  The exact Lean form of this Prop was agreed with Worker 5424, whose comparison
  theorem for item 5 takes its two conjuncts at `i = Φ τ₀` as hypotheses.

  It is the classical description of the `p`-adic embeddings of an unramified
  extension. Group the embeddings `K → Q̄_p` by the place `w` they induce. Those
  inducing `w` are the `ℚ_p`-embeddings of the completion `K_w`, and there are
  `[K_w : ℚ_p] = e_w f_w` of them. When `K_w/ℚ_p` is unramified, `Gal(Q̄_p/ℚ_p)`
  acts on them through the cyclic group `Gal(K_w^{gal}/ℚ_p)`, which Frobenius
  generates. This is a free transitive action, so the Frobenius orbits are the
  fibres and have `f_w` elements. This is standard: see Neukirch, *Algebraic
  Number Theory*, Ch. II, which covers extensions of valuations, completions
  and unramified extensions. This module does not prove the Prop.
- `harrisPlaceFibre p θ w : Finset (K →+* ℂ)` is the fibre of the place map over
  a place `w ∣ p`: the embeddings `i` with `harrisPlace p θ i = w`.
- `cocharExtend a : S × Bool → Fin n → ℤ` extends the free coordinates
  `a = (a₀, (a_{τ,k}))` of a cocharacter of Kottwitz's diagonal torus to all CM
  indices: `(τ, true) ↦ a_{τ,k}` and `(τ, false) ↦ a₀ − a_{τ, rev k}`. These are
  the exponents at the embedding `Φ τ` and at its conjugate. This is the inverse
  of the relation `m_{w,k} + m_{w̄, rev k} = m_c` that defines
  `localCocharacters`.

## Results and proofs

### Galois automorphisms preserve places

- `padicAlgCl_valuation_algEquiv`: every `σ ∈ Gal(Q̄_p/ℚ_p)` preserves the
  valuation of `Q̄_p`. The norm of `Q̄_p` is the spectral norm
  (`PadicAlgCl.spectralNorm_eq`), and Mathlib's `spectralNorm_eq_of_equiv` shows
  that the spectral norm is Galois invariant.
- `harrisPrime_frobeniusPerm`, `harrisPlace_frobeniusPerm`,
  `harrisPlace_frobeniusPerm_pow`: `harrisPlace p θ (Frob^r ∘ i) = harrisPlace p θ i`.
  Because `θ(Frob·i(x)) = Frob(θ(i(x)))` (`theta_frobeniusPerm_apply`), membership
  in the two primes has the same valuation condition.
- `harrisPlace_surjective`: every place of `K` above `p` is `harrisPlace p θ i`
  for some `i`. This is the Library's `range_harrisPrime` together with
  `liesOver_rationalPrimePlace_iff`.
- `mem_harrisPlaceFibre`, `harrisPlaceFibre_nonempty`,
  `frobeniusPerm_pow_mem_harrisPlaceFibre`: the fibres are nonempty and stable
  under every power of Frobenius.
- `sum_card_harrisPlaceFibre`: `∑_{w ∣ p} #fibre(w) = [K : ℚ]`. The fibres
  partition the `[K : ℚ]` complex embeddings (`NumberField.Embeddings.card`,
  `Finset.card_eq_sum_card_fiberwise`).

### Conjugation (`K` a CM field, `E` its totally real subfield)

- `harrisPlace_conjugate E`: `harrisPlace p θ (conj ∘ i) = placeConj (harrisPlace p θ i)`.
  `placeConj` (module `KottwitzChart`) is the conjugate place, made of the
  integers whose CM conjugate lies in `w`. The proof uses
  `conj ∘ i = i ∘ c` (`conjugate_apply`) with `c` the CM involution. Then both
  conditions read `|θ(i(c x))|_p < 1`.
- `conjugate_mem_harrisPlaceFibre E`: conjugation maps the fibre over `w` onto
  the fibre over `w̄`.
- `embeddingCochar_injective hΦ n`: `embeddingCochar θ Φ`, the map
  `(m, m_c) ↦ (m_c, (m_{w(Φτ), k}))`, is injective on `localCocharacters`.
  Proof: every place `w` is `harrisPlace p θ i`, and `i` is either `Φ τ` or
  `conj ∘ Φ τ` (`cmFactorEmbeddingEquiv` is onto). In the first case `m_{w,k}` is
  a coordinate of `embeddingCochar`. In the second, `w = w(Φτ)‾` and
  `m_{w,k} = m_c − m_{w(Φτ), rev k}`.

### Rationality of Frobenius-invariant cocharacters

- `cocharExtend_cmSwap`: `ext(a)(x̄, k) = a₀ − ext(a)(x, rev k)`.
- `cocharExtend_apply_of_cocharPullback_eq`: if `cocharPullback n G a = a`, then
  `ext(a)(G x) = ext(a)(x)` for every CM index `x`. At `x = (τ, true)` this is
  the defining formula of `cocharPullback` read through
  `G(τ, true) = (base G τ, !crosses G τ)` (`CMPerm.apply_eq`). At `(τ, false)` it
  follows from `G` commuting with `cmSwap` and from `cocharExtend_cmSwap`.
- `frobeniusInvariantsRational_of_frobeniusOrbitsArePlaces hΦ n h`:
  `FrobeniusOrbitsArePlaces K p θ → FrobeniusInvariantsRational E K n p θ hΦ`.
  Proof: let `a` be fixed by the pullback along `frobeniusCMPerm hΦ θ`. Put
  `b(i) = ext(a)(index of i)`. Then `b(Frob ∘ i) = b(i)`, by the previous lemma and
  `CMPerm.ofEmbeddingPerm_apply`, so `b` is constant on Frobenius orbits. By the
  hypothesis, `b` is then constant on the fibres of the place map. Choose an
  embedding `i_w` in each fibre and set `m_{w,k} = b(i_w)(k)` and `m_c = a₀`.
  The relation `m_{w,k} + m_{w̄, rev k} = a₀` holds because `conj ∘ i_w` lies
  over `w̄` and `b(conj ∘ i)(k) = a₀ − b(i)(rev k)`. Finally
  `embeddingCochar θ Φ m = a`, because `Φ τ` lies in the fibre over `w(Φ τ)` and
  `b(Φ τ) = a_τ`.

Together with `embeddingCochar_injective`, this turns the two hypotheses of
`kottwitzPolynomialOf_eq_of_isNormalizedLift` and `exists_isNormalizedLift`
(module `KottwitzLiftIndependence`) into the single hypothesis
`FrobeniusOrbitsArePlaces K p θ`.

## Provenance

The Lean statements are internal. They are elementary facts about the Library's
objects `harrisPlace`, `frobeniusPerm`, `placeConj`, `localCocharacters` and
`embeddingCochar`, and they are needed to use the results of
`KottwitzLiftIndependence` without hypotheses. The mathematical content is
standard: Galois invariance of the `p`-adic absolute value on `Q̄_p`, and the
description of the embeddings of an unramified local field cited above
(Neukirch, *Algebraic Number Theory*, Ch. II). That description is stated as
`FrobeniusOrbitsArePlaces` and is not proved here.
