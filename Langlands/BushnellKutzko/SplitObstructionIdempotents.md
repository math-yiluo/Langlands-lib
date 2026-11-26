# Idempotents attached to a split fundamental stratum

Module `Langlands.BushnellKutzko.SplitObstructionIdempotents`. Let `E` be a finite extension
of a nonarchimedean local field `F` and `𝔬_E = subfieldIntegers F E`. A split fundamental
stratum over `𝔬_E` (`Stratum.IsSplit`, BK93 (2.3.3), printed p. 58) gives two complementary
nonzero idempotents of its order. They commute with the element of the stratum, and the
commutator with that element is injective on each graded step of the off-diagonal block.
Bushnell–Kutzko (1993) obtain the corresponding splitting in (2.3.9)–(2.3.10), printed
p. 60, from [K4] (3.4), under `gcd(n, e) = 1`; the proof of (2.3.12) first coarsens the
chain to reach that case. The construction here needs no coarsening. It uses the element
`y_b = π^{n/g} b^{e/g}` of the published `Stratum.fundamentalElement` directly, and deduces
graded injectivity, the content of (2.3.8)(iii) used in (2.3.12), from an idempotent that
is a polynomial in `y_b` with coefficients in `𝔬_E`.

## General lemmas

- `reduceIntegralPolynomial_map`: for an injective `algebraMap O K`, applying the published
  `reduceIntegralPolynomial O K` to the image of `Φ ∈ O[X]` gives `Φ` reduced modulo
  `Ring.jacobson O`.
- `exists_integral_charpoly`: over a principal ideal domain `O` with fraction field `K`, an
  endomorphism of `V` preserving a lattice `M` has a characteristic polynomial that is the
  image of a monic polynomial over `O`. This is the characteristic polynomial of the
  restriction to `M`, computed in a basis of `M` (`Module.Basis.extendOfIsLattice`).
- `not_isUnit_aeval_of_dvd_charpoly`: if `h ∈ K[X]` has positive degree and divides the
  characteristic polynomial of `x`, then `h(x)` is not invertible. A root of `h` in an
  algebraic closure is an eigenvalue of the matrix of `x`, and `h(x)` has `0` in its spectrum
  (`spectrum.subset_polynomial_aeval`).
- `exists_coprime_split`: a monic polynomial over a field with two distinct monic
  irreducible divisors `p ≠ q` is a product `p^m · c` of coprime monic factors of positive
  degree, where `m` is the multiplicity of `p`.

## The integer ring and the chain

- `henselianRing_subfieldIntegers`: `𝔬_E` is Henselian along `Ring.jacobson 𝔬_E`. The
  published `subfieldIntegerEquiv` identifies it with `𝒪[E]` for the local-field structure of
  `Langlands.LocalField.FiniteExtension`. `𝒪[E]` is `𝓂[E]`-adically complete in Mathlib, and
  complete rings are Henselian (`IsAdicComplete.henselianRing`).
- For an `𝔬_E`-lattice chain `𝓜` and a prime element `π` (`RingPrimeElement`):
  `prime_smul_mem_lattice`, `prime_inv_smul_mem_lattice` and `prime_zpow_smul_mem_lattice`
  show that `π^k` maps `L_i` into `L_{i+k·e}` for all `k ∈ ℤ`, with `e` the period.
  `prime_zpow_smul_mem_endFiltration` is the corresponding shift of the filtration, and
  `pow_mem_endFiltration` gives `x^k ∈ 𝔔^{k m}` for `x ∈ 𝔔^m`.
- `fundamental_exponents`: `n · (e/g) = (n/g) · e` for `g = gcd(e, |n|)`.
  `fundamentalElement_mem_order`: if `b ∈ 𝔔^{−n}`, then `y_b ∈ 𝔔^0`.

## Main theorem

`exists_split_idempotents`. Let `D` be a stratum over `𝔬_E` with `D.IsSplit` and
`D.b ∈ 𝔔^{−D.n}`. Then there are `e₁, e₂ ∈ End_E(V)` such that:

- `e₁ + e₂ = 1`, `e₁ e₂ = 0`, `e₁ ≠ 0`, `e₂ ≠ 0`, both lie in `𝔔^0`, and both commute with
  `D.b`;
- for every `i` and every `x ∈ 𝔔^i` with `e₁ x e₂ = x`, if
  `D.b x − x D.b ∈ 𝔔^{i−D.n+1}`, then `x ∈ 𝔔^{i+1}`.

Proof:

1. The characteristic polynomial of `Y = y_b` is the image of a monic `Φ ∈ 𝔬_E[X]`. Its
   reduction is the published `fundamentalPolynomial`.
2. The split hypothesis gives a coprime factorization of that reduction into monic factors
   of positive degree. The Henselian lemma `ValuationTheory.Henselian.exists_coprime_factor_lift`
   lifts it to `Φ = f₁ f₂`, with `f₁, f₂` monic, coprime in `𝔬_E[X]`, of positive degree.
3. Write `u f₁ + v f₂ = 1` and put `e₁ = (v f₂)(Y)` and `e₂ = (u f₁)(Y)`. Then
   `e₁ + e₂ = 1`, and `e₁ e₂ = 0` by Cayley–Hamilton (`LinearMap.aeval_self_charpoly`).
   Polynomials in `Y` over `𝔬_E` lie in the order, and they commute with `D.b`, since `Y`
   does.
4. If `e₁ = 0`, then `f₁(Y)` would be invertible. This contradicts
   `not_isUnit_aeval_of_dvd_charpoly`. The same argument with `f₂` shows `e₂ ≠ 0`.
5. Graded injectivity. If `b x − x b ∈ 𝔔^{i−n+1}`, then `b^k x − x b^k ∈ 𝔔^{i+1−nk}`.
   Multiplying by `π^{n/g}` gives `Y x − x Y ∈ 𝔔^{i+1}`. The elements `z ∈ 𝔔^0` with
   `z x − x z ∈ 𝔔^{i+1}` form an `𝔬_E`-subalgebra containing `Y`, hence containing `e₂`.
   For `x = e₁ x e₂` we have `e₂ x − x e₂ = −x`, so `x ∈ 𝔔^{i+1}`.
