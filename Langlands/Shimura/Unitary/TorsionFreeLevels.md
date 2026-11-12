# Torsion-free principal congruence levels

Author: Worker 19.

Let `A` be a finite-dimensional `ℚ`-algebra with involution `σ`, and let
`v` be a finite place of `ℚ` lying over a prime `q ≥ 3`. This module
constructs an open subgroup of the local similitude group `σ(ℚ_v)` whose
only element of finite order is `1`: the principal congruence level modulo
`q`. Such a subgroup is what makes a level "sufficiently small" in the sense
of Harris and Taylor.

## Source

Harris and Taylor (2001), Chapter III, Section 1, printed p. 90 (PDF p. 98):
"Let `U` be a sufficiently small open compact subgroup of `G(A^∞)`. By
sufficiently small we shall mean that the projection of `U` to `G(ℚ_x)` for
some prime `x` contains no element of finite order other than 1."

Harris (1999), Section 4, printed p. 310 (PDF p. 12), requires "that
`K^{ℓ,p}` is sufficiently small so that (4.5)" holds.

Neither source proves that such levels exist. The construction and the
proof here are the standard argument for principal congruence subgroups,
written for this module.

## Setting

- `σ : AlgebraInvolution ℚ A`, with `A` finite over `ℚ`. For a finite place
  `v`, `ℚ_v` is the published `FiniteCompletion ℚ v`, `𝒪_v` is
  `v.adicCompletionIntegers ℚ`, and `σ(ℚ_v)` is the published
  `σ.Points (FiniteCompletion ℚ v)`. Its elements are pairs `(g, c)` with
  `g ∈ (ℚ_v ⊗ A)^×`, `c ∈ ℚ_v^×` and `g σ(g) = c`.
- `q` is a natural number with `(q) ⊆ v` (the hypothesis
  `(q : 𝓞 ℚ) ∈ v.asIdeal`). The main results assume `q` prime and `q ≥ 3`.

## Declarations

### Generic descent (any ring `R`)

`powMul Λ q k` is the additive subgroup `q^k Λ` for a non-unital subring
`Λ` of a ring `R`. The basic lemmas are `mem_powMul`, `powMul_mono`
(`q^k Λ ⊆ q^j Λ` for `j ≤ k`), `mul_mem_powMul`
(`q^j Λ · q^k Λ ⊆ q^{j+k} Λ`), `mul_mem_powMul_of_mem`, `pow_succ_mem_powMul`
and `mem_powMul_of_natCast_pow_mul`. The last one cancels `q^k` when
multiplication by `q` is injective on `R`.

- `one_add_pow_sub_one_mem`: if `x ∈ q^k Λ` then `(1 + x)^n - 1 ∈ q^k Λ`.
- `one_add_pow_sub_mem`: if `x ∈ q^a Λ` then
  `(1 + x)^m - 1 - m x ∈ q^{2a} Λ`, by induction on `m` using
  `(1 + x)^{m+1} - 1 - (m+1) x = ((1 + x)^m - 1 - m x)(1 + x) + m x²`.
- `one_add_pow_prime_sub_mem`: for prime `q` and `x ∈ q^a Λ`,
  `(1 + x)^q - 1 - q x - x^q ∈ q^{2a+1} Λ`. It uses Mathlib's
  `Commute.add_pow_prime_eq`: the middle binomial coefficients are
  divisible by `q`.
- `mem_powMul_succ_of_pow_eq_one`: let `q ≥ 3` be prime and multiplication
  by `q` injective on `R`. If `x ∈ q^a Λ` with `a ≥ 1` and `(1 + x)^r = 1`
  for a prime `r`, then `x ∈ q^{a+1} Λ`.
  - Proof: write `x = q^a y` with `y ∈ Λ`. It suffices that `y ∈ q Λ`.
    If `r ≠ q`, then `r x ∈ q^{2a} Λ` by `one_add_pow_sub_mem`, so
    `r y ∈ q Λ`. Writing `u r + w q = 1` (Bezout), `y = u (r y) + w (q y)`
    lies in `q Λ`. If `r = q`, then
    `q x = -((1 + x)^q - 1 - q x - x^q) - x^q`. The first term lies in
    `q^{2a+1} Λ` and `x^q` in `q^{qa} Λ`, both inside `q^{a+2} Λ` because
    `a ≥ 1` and `q ≥ 3`. Thus `q^{a+1} y ∈ q^{a+2} Λ` and `y ∈ q Λ`.
- `eq_zero_of_one_add_pow_eq_one`: let `q ≥ 3` be prime, multiplication by
  `q` injective on `R`, and `⋂_k q^k Λ = 0`. If `x ∈ q Λ` and
  `(1 + x)^m = 1` with `m > 0`, then `x = 0`.
  - Proof: strong induction on `m`. For `m = 1` it is immediate. Otherwise
    let `r` be the least prime factor of `m` and `m = m' r`. Then
    `x' = (1 + x)^{m'} - 1 ∈ q Λ` satisfies `(1 + x')^r = 1`, so by the
    previous lemma `x' ∈ q^k Λ` for every `k`, hence `x' = 0`. So
    `(1 + x)^{m'} = 1` with `m' < m`, and the induction hypothesis applies.
- `eq_one_of_isOfFinOrder`: the same statement for an element `g` of
  finite order with `g - 1 ∈ q Λ`: then `g = 1`.
- `mul_sub_one_mem`: `1 + q Λ` is closed under multiplication.

### The local order

- `matrixSubring O`: the subring of square matrices with entries in a
  subring `O` (`mem_matrixSubring`).
- `localBasis A v` is the basis `1 ⊗ b` of `ℚ_v ⊗ A` over `ℚ_v`, where `b`
  is Mathlib's `Module.finBasis ℚ A`.
- `localOrder A v`: the elements `x ∈ ℚ_v ⊗ A` whose left multiplication
  matrix `Algebra.leftMulMatrix (localBasis A v) x` has entries in `𝒪_v`.
  It is a subring because `leftMulMatrix` is a ring homomorphism.
- `valued_natCast_lt_one`: if `(q) ⊆ v` then `|q|_v < 1`.
- `natCast_mul_eq_zero`: multiplication by a nonzero natural number is
  injective on `ℚ_v ⊗ A`, because it is a unit in a `ℚ`-algebra.
- `eq_zero_of_forall_mem_powMul_localOrder`: if `(q) ⊆ v`, then
  `⋂_k q^k Λ_v = 0`. If `x ∈ q^k Λ_v`, every entry of the left
  multiplication matrix of `x` has valuation at most `|q|_v^k`. A nonzero
  entry would contradict `|q|_v^k → 0` (Mathlib's `exists_pow_lt₀`), so the
  matrix is zero and `x = 0` because `leftMulMatrix` is injective.

### The principal congruence level

- `congruenceLevel σ v q`: the points `(g, c)` of `σ(ℚ_v)` with
  `g - 1 ∈ q Λ_v` and `g⁻¹ - 1 ∈ q Λ_v`. It is a subgroup by
  `mul_sub_one_mem`. Both conditions are imposed because `Λ_v` need not
  contain inverses.
- `isOpen_congruenceLevel`: for `q ≠ 0` the level is open. `Λ_v` is open in
  the module topology of `ℚ_v ⊗ A`, being the preimage of the open set of
  integral matrices under the continuous linear map `leftMulMatrix`. The
  condition `b - 1 ∈ q Λ_v` means `q⁻¹ (b - 1) ∈ Λ_v`, and `g ↦ g`,
  `g ↦ g⁻¹` are continuous on the points.
- `congruenceLevel_torsionFree`: for `A ≠ 0`, a prime `q ≥ 3` with
  `(q) ⊆ v`, and `(g, c)` of finite order in the level, `(g, c) = 1`.
  `eq_one_of_isOfFinOrder` gives `g = 1`. Then `c = g σ(g) = 1`, because
  `ℚ_v → ℚ_v ⊗ A` is injective when `A ≠ 0`.
- `exists_isOpen_torsionFree`: the resulting existence statement: `σ(ℚ_v)`
  has an open subgroup whose only element of finite order is `1`.

## Scope

- **Prime `q ≥ 3`.** For `q = 2` the level modulo `2` can contain `-1`; the
  level modulo `4` would be needed and is not treated. Any choice of place
  over an odd prime suffices for Harris's smallness condition.
- **Local statement only.** The module does not pass to adelic levels.
  Intersecting a compact open level with the preimage of the congruence
  level at one place, and the resulting (4.5), are not done here.
- **The order depends on a basis.** `localOrder` uses Mathlib's chosen
  basis of `A`. Only its properties are used, not its independence of the
  basis.
- **Compactness.** The congruence level is proved open; its compactness is
  not proved here.

## Provenance

The sources are Harris and Taylor (2001), printed p. 90, and Harris (1999),
printed p. 310, read in the original (rendered pages). They state the
smallness condition but do not prove that small levels exist. The
congruence construction and the descent argument (Bezout for primes other
than `q`, and the binomial estimate requiring `q ≥ 3`) are the standard
proof that principal congruence subgroups are torsion-free, written for this
module.

Source IDs and SHA-256 fingerprints:

- `harris-taylor-2001-geometry-cohomology-simple-shimura`:
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies:

- the published `Langlands.Shimura.Unitary.Adelic` (`Points`, its group and
  topology), with `Similitude` (`similitudes`, `mem_similitudes_iff`) and
  `Involution` (`baseChange`, `apply_one`);
- the published `Langlands.Global.Adelic` (`FinitePlace`,
  `FiniteCompletion`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in
  particular `Commute.add_pow_prime_eq`, `Algebra.leftMulMatrix`,
  `Algebra.leftMulMatrix_injective`, `Algebra.TensorProduct.basis`,
  `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation`,
  `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`,
  `exists_pow_lt₀`, `Valued.isOpen_valuationSubring`,
  `IsModuleTopology.continuous_of_linearMap`,
  `IsModuleTopology.isTopologicalRing` and
  `Algebra.TensorProduct.includeRight_injective`.
