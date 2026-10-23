# Norms of ideals prime to `m` lie in the Galois image

Let `L / K` be a Galois extension of number fields, and let `ζ ∈ L` be a primitive `m`-th
root of unity, with `m ≠ 0`. The Galois group acts on `ζ` by `ζ ↦ ζ^c`, so it maps to
`(ℤ/m)ˣ`. This module shows two things.

- For a nonzero prime `P` of `𝓞 K` not dividing `m`, the class of the norm `N(P)` lies in
  the image of `Gal(L/K)`.
- Fix a finite set `T` of primes containing those dividing `m`. For a nonzero ideal `I` of
  `𝓞 K`, the product of the cyclotomic symbols at the primes outside `T`, evaluated at
  `N(I)`, lies in that image.

This is the unramified part of the Artin–Tate norm argument in the reciprocity proof for
cyclic cyclotomic extensions (task fb66219f). Every declaration is in the namespace
`Langlands.Global.CyclotomicSymbol`.

## Definitions

- `galoisImage K hζ : Subgroup (ZMod m)ˣ` is the range of Mathlib's
  `IsPrimitiveRoot.autToPow K : Gal(L/K) →* (ZMod m)ˣ`. Here `σ ζ = ζ ^ c` with
  `c = autToPow σ`.
- `natUnit n hn : ℚˣ` is a nonzero natural number viewed as a rational unit.
- `outsideSymbol m T : ℚˣ →* (ZMod m)ˣ` sends `α` to the product
  `∏ᶠ p : Nat.Primes, (if p ∈ T then 1 else primeSymbol m p α)`.
  `primeSymbol` is the local cyclotomic symbol of `Langlands.Global.Arithmetic.CyclotomicSymbol`.
  Only finitely many factors differ from `1` (`mulSupport_outside_subset`), so the product
  is a homomorphism.
- The instance `infinite_ringOfIntegers : Infinite (𝓞 K)`, from `ℤ ↪ 𝓞 K`. The Mathlib
  results on absolute norms used here require it.

## Theorems

- `exists_autToPow_eq_card`: let `P` be a nonzero prime of `𝓞 K` with `m ∉ P`. Then some
  `σ ∈ Gal(L/K)` has `autToPow σ = N(P) mod m`, where `N(P) = |𝓞 K / P|`. Proof:
  - Choose a prime `Q` of `𝓞 L` over `P` (going up). Mathlib's
    `IsArithFrobAt.exists_of_isInvariant` gives an arithmetic Frobenius `σ` at `Q`. Galois
    invariance of `𝓞 L` over `𝓞 K` is Mathlib's `IsGaloisGroup` instance.
  - Since `m ∉ Q`, `IsArithFrobAt.apply_of_pow_eq_one` gives `σ ζ = ζ ^ N(P)`.
  - Comparing with `ζ ^ c = σ ζ`, the exponents agree modulo the order `m` of `ζ`.
- `coprime_card_of_not_mem`: if `m ∉ P`, then `N(P)` is coprime to `m`. The residue field
  has characteristic `ℓ ∤ m` and order a power of `ℓ`.
- `unitOfCoprime_card_mem`: the unit class of `N(P)` lies in `galoisImage K hζ`.
- `primeSymbol_of_not_mem`: if `T` contains every prime dividing `m` and `p ∉ T`, then
  `primeSymbol m p α = p ^ v_p(α)`.
- `outsideSymbol_primePow`: for a prime `ℓ`,
  `outsideSymbol m T (ℓ^f) = 1` if `ℓ ∈ T`, and the class of `ℓ^f` otherwise.
- `outsideSymbol_absNorm_mem`: if `T` contains every prime dividing `m`, then
  `outsideSymbol m T (N(I)) ∈ galoisImage K hζ` for every nonzero ideal `I` of `𝓞 K`.
  The proof inducts on the prime factorization of `I`
  (`UniqueFactorizationMonoid.induction_on_prime`). The norm `N(P) = ℓ^f` of a nonzero
  prime factor contributes `1` when `ℓ ∈ T`. When `ℓ ∉ T` it contributes the class of
  `N(P)`, which lies in the image by `unitOfCoprime_card_mem`.

## Sources and provenance

This is the unramified ingredient of Artin–Tate's Chapter VII §2. Theorem 2 is on printed
p.39 (PDF p.48), and its proof continues on printed p.40 (PDF p.49). There, for `p ∤ m`, the
`p`-component of a norm has ordinal a multiple `r n_p` of the local degree, and `σ_p` acts on
`ζ` like the Frobenius power `φ_p^{r n_p}`, which fixes `K`. Artin–Tate work over `ℚ`. Here
the base is a general number field `K`, and the statement is in terms of ideal norms, so
that it combines with the product formula over `ℚ`.

Provenance is derived. The ideal-norm formulation and the outside-`T` product are internal
choices that avoid local valuations at the unramified places.
