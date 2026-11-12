# Primes cut out by complex embeddings and Harris's set `Φ_p`

Author: Worker 19.

Harris attaches to the CM type `Φ` of the CM field `𝒦` a set `Φ_p` of primes
of `𝒦` above `p`, by comparing complex and `p`-adic embeddings. This module
defines `Φ_p` and proves its basic properties. For Harris's type, induced from
an embedding of the imaginary quadratic subfield `𝒦₀`, the results are:

- `Φ_p` is the set of primes of `𝒦` above the prime `u` of `𝒦₀` cut out by
  that embedding.
- Its conjugate set `c(Φ_p)` is the set of primes of `𝒦` above `ū`.
- The primes of `𝒦₀` above `p` are exactly `u` and `ū`.
- `Φ_p` and `c(Φ_p)` are disjoint exactly when `p` splits in `𝒦₀`.

The underlying construction is general. An embedding of a number field into
an algebraically closed valued field defines a prime of the field. Every prime
above the prime of an embedding of a subfield comes from an extension of that
embedding.

## Source

Harris (1999), Section 4, printed pp. 308-309 (PDF pp. 10-11): "Thus `𝒦` is
assumed to contain an imaginary quadratic field `𝒦₀`, and we choose `Φ` to be
the CM type of `𝒦` consisting of all complex embeddings inducing a chosen
complex embedding `1_{𝒦₀}` of `𝒦₀`. We assume `p` splits in `𝒦₀`. … The CM
type `Φ` corresponds to a set of primes `Φ_p` of `𝒦` above `p`, via the
identification `𝒦 ≅ E(GG, X_{n-1})` (cf. [H1]), and we assume `v ∈ Φ_p`. Let
`Φ_p = {v^(j), j = 1, …, t}`, and write `𝒟_p = ∏_{j=1}^t 𝒟_j × ∏_{j=1}^t c(𝒟_j)`;
here `𝒟_j = 𝒟 ⊗ 𝒦_{v^(j)}` and `c` denotes complex conjugation."

Harris (1997) (= [H1]), Section 2, printed p. 89 (PDF p. 15): "In order to
describe the `p`-adic uniformization, we need a way to compare complex and
`p`-adic embeddings of `𝒦`. We let `Q̄` be the algebraic closure of `Q` in
`C`, and we fix an embedding `φ: Q̄ ↪ Q̄_p`. Let `Φ` be the set of embeddings
`η: 𝒦 ↪ Q̄` such that `φ ∘ η` induces the prime `𝔭₁` of `𝒦₀`. Then `Φ` is a
CM type of `𝒦`." On printed p. 88, `p = 𝔭₁ · 𝔭₂` splits in `𝒦₀`.

Harris 1999 does not spell out the correspondence. As in Harris 1997, a
complex embedding `η ∈ Φ` gives the prime of `𝒦` on which `φ ∘ η` has
absolute value less than one. `Φ_p` is the set of these primes, and Harris's
`c(𝒟_j)` are the factors at their complex conjugates.

## Declarations

All declarations are in namespace `Langlands.Shimura`.

### Primes of embeddings

Let `C` be a field with a valuation `v : Valuation C Γ₀`, and `K` a field.

- `valuation_embedding_le_one`: for `φ : K →+* C` and `x` in the ring of
  integers `𝓞 K`, `v (φ x) ≤ 1` (algebraic integers are integral over `ℤ`).
- `embeddingIdeal v φ` is the ideal `{x ∈ 𝓞 K | v (φ x) < 1}`
  (`mem_embeddingIdeal`). It is prime (`embeddingIdeal_isPrime`) and contains
  every natural number `p` with `v p < 1` (`natCast_mem_embeddingIdeal`).
- For a field extension `F → K` (`[Algebra F K]`), `under_embeddingIdeal`: the
  contraction of `embeddingIdeal v φ` to `𝓞 F` is the ideal of the restriction
  `φ ∘ (F → K)`. Hence `liesOver_embeddingIdeal`, an instance.

Now let `F` and `K` be number fields.

- `embeddingIdeal_ne_bot`: if `p ≠ 0` and `v p < 1`, the ideal is nonzero.
- `embeddingPrime v φ hp0 hp` is the ideal as a finite place
  (`HeightOneSpectrum (𝓞 K)`), with `embeddingPrime_asIdeal`.
- `comap_galRestrict_embeddingIdeal`: for a number field `M` over `F`, an
  embedding `ψ : M →+* C` and `g ∈ Gal(M/F)`, the pullback of
  `embeddingIdeal v ψ` along the restriction of `g` to `𝓞 M` is the ideal of
  `ψ ∘ g`.

Assume moreover that `C` is algebraically closed.

- `exists_embedding_of_liesOver`: for `χ : F →+* C` and a prime `w` of `𝓞 K`
  lying over `embeddingIdeal v χ`, there is `φ : K →+* C` with
  `φ ∘ (F → K) = χ` and `w = embeddingIdeal v φ`.
- `rat_prime_eq_of_natCast_mem`: for a prime number `p`, two prime ideals of
  `𝓞 ℚ` containing `p` are equal.
- `exists_embedding_of_natCast_mem`: if `C` has characteristic zero, `p` is
  prime and `v p < 1`, every prime `w` of `𝓞 K` containing `p` is
  `embeddingIdeal v φ` for some `φ : K →+* C`.

### Harris's primes

Fix a prime number `p` and a ring homomorphism `θ : ℂ →+* Q̄_p`, where
`Q̄_p = PadicAlgCl p` is Mathlib's algebraic closure of `ℚ_p`.

- `harrisValuation p θ` is the valuation `z ↦ |θ z|_p` on `ℂ`. It is the
  pullback along `θ` of Mathlib's valuation `PadicAlgCl.valued` on `Q̄_p`,
  which is the extension of the `p`-adic norm (`harrisValuation_apply`).
  `harrisValuation_natCast_lt_one`: `|θ p|_p = 1/p < 1`.
- `harrisPrime p θ φ`, for a number field `K` and `φ : K →+* ℂ`, is the
  finite place `embeddingPrime` of `φ` for this valuation: the integers `x`
  with `|θ (φ x)|_p < 1` (`harrisPrime_asIdeal`). It lies above `p`
  (`natCast_mem_harrisPrime`).
- `range_harrisPrime`: the places `harrisPrime p θ φ` are exactly the finite
  places of `K` containing `p`.
- For number fields `F → K`, `liesOver_harrisPrime` (an instance): the prime
  of `φ` lies over the prime of `φ ∘ (F → K)`.
  `harrisPrime_liesOver_iff`: a finite place `w` of `K` lies over the prime of
  `τ : F →+* ℂ` if and only if `w = harrisPrime p θ φ` for some `φ` extending
  `τ`.
- `cmTypePrimes p θ Φ`, for a CM field `K` and a CM type `Φ` (the published
  `Global.CMType`), is the image of `Φ` under `harrisPrime p θ`. This is
  Harris's `Φ_p` (`mem_cmTypePrimes`).
- `cmTypePrimes_union_conjugate`: `Φ_p` together with the set of the
  conjugate type `Φ.conjugate` is the set of all finite places of `K`
  containing `p`.

### Complex conjugation

Let `K` be a CM field.

- `conjPrime w` is the image of a finite place `w` under complex conjugation.
  It is the pullback of `w` along Mathlib's
  `IsCMField.ringOfIntegersComplexConj K` (`conjPrime_asIdeal`).
  `conjPrime_conjPrime`: this is an involution.
- `harrisPrime_conjugate`: the prime of the conjugate embedding `φ̄` is the
  conjugate of the prime of `φ`.
- `cmTypePrimes_conjugate`: the primes of `Φ.conjugate` are the conjugates
  `c(Φ_p)` of the primes of `Φ`.

### Harris's CM type

Let `F` be an imaginary quadratic field (`[IsCMField F]`,
`[Algebra.IsQuadraticExtension ℚ F]`) and `τ : F →+* ℂ`. Write `u` for
`harrisPrime p θ τ` and `ū` for `harrisPrime p θ τ̄`.

- `eq_or_eq_conjugate_of_quadratic`: every complex embedding of `F` is `τ` or
  `τ̄`.
- `inducedFromImaginaryQuadratic_conjugate`: for `ι : F →+* K` with `K` CM,
  the conjugate of the published `CMType.inducedFromImaginaryQuadratic ι τ` is
  the type induced from `τ̄`.
- `setOf_natCast_mem_eq_pair`: the finite places of `F` containing `p` are
  exactly `u` and `ū`.
- `ncard_setOf_natCast_mem_eq_two_iff`: there are exactly two of them,
  i.e. `p` splits in `F`, if and only if `u ≠ ū`.

Now let `K` be a CM field over `F` and
`Φ = CMType.inducedFromImaginaryQuadratic (algebraMap F K) τ`, Harris's type
(`1_{𝒦₀} = τ`).

- `cmTypePrimes_inducedFromImaginaryQuadratic`: `Φ_p` is the set of finite
  places of `K` lying over `u`.
- `cmTypePrimes_conjugate_inducedFromImaginaryQuadratic`: the set of
  `Φ.conjugate` is the set of finite places of `K` lying over `ū`.
- `disjoint_cmTypePrimes_conjugate_iff`: the two sets are disjoint if and only
  if `u ≠ ū`, i.e. `p` splits in `F`.
- `mem_inducedFromImaginaryQuadratic_iff`: if `u ≠ ū`, an embedding
  `σ : K →+* ℂ` lies in `Φ` if and only if the prime of `σ ∘ (F → K)` is `u`.
  This is Harris 1997's definition of `Φ`, with `𝔭₁ = u`. By
  `setOf_natCast_mem_eq_pair`, a given prime `𝔭₁` of `F` above `p` equals `u`
  for `τ` or for `τ̄`.

## Comparison with the source

- Harris 1997 fixes `φ : Q̄ ↪ Q̄_p` on the algebraic closure of `ℚ` in `ℂ`.
  Here the input is a ring homomorphism `θ : ℂ →+* Q̄_p`. The definitions use
  `θ` only on the images of complex embeddings of number fields, which are
  algebraic numbers. Extending a given `φ` to `ℂ` is not formalized.
- Harris 1999 writes the correspondence through the reflex field
  identification `𝒦 ≅ E(GG, X_{n-1})`. The reflex field and this
  identification are not used here; `Φ_p` is defined directly from `Φ` and `θ`.
- Harris's assumptions `v ∈ Φ_p` and that `p` splits are not imposed. They
  are hypotheses for later uses, and the last group of results characterizes
  splitting as `u ≠ ū`.

## Scope

The module concerns only primes and CM types. It makes no statement about the
algebras `𝒟_j`, the groups `GG` and `GJ`, or the Shimura variety. It does not
connect `Φ_p` with the places used in `HarrisSplitPrimeFactors` or
`HarrisDivisionLevels`.

## Provenance

Derived from Harris (1999), Section 4, printed pp. 308-309, and Harris
(1997), Section 2, printed pp. 88-89, both read in the original. The general
statements about primes of embeddings are standard algebraic number theory and
are needed to state and prove the Harris results. The existence proof passes
through a Galois closure, Mathlib's `IntermediateField.normalClosure` inside
`AlgebraicClosure K`; this choice affects only the proof.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-1997-drinfeld-cohomology`:
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.

Formal dependencies: the published `Langlands.Global.CMType`, and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0. The Mathlib
results used include `Valuation.Integers.isIntegral_iff_v_le_one`,
`Ideal.exists_ideal_over_prime_of_isIntegral`, `Ideal.exists_comap_galRestrict_eq`,
`IsAlgClosed.lift`, `PadicAlgCl.valuation_p`,
`NumberField.IsCMField.complexEmbedding_complexConj`,
`NumberField.ComplexEmbedding.lift` and `HeightOneSpectrum.comap`.
