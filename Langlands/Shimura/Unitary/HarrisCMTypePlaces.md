# Harris's split-prime data from the CM type

Author: Worker 19.

The published split-prime units take a place `𝔭` of the imaginary quadratic
field `F` above a rational place `v`, a proof that the completion map
`ℚ_v → F_𝔭` is bijective, and a distinguished place `w₀` of the CM field `K`
above `𝔭` as free parameters. Here these parameters are supplied from Harris's
data, using `HarrisCMTypePrimes`:

- `v` is the place of `ℚ` at `p`;
- `𝔭` is the prime `u` of `F` cut out by `θ ∘ τ`, for `θ : ℂ →+* Q̄_p` and the
  chosen embedding `τ = 1_{𝒦₀}`;
- the bijectivity comes from `p` splitting in `F`, i.e. `u ≠ ū`;
- the places of `K` above `u` are Harris's `Φ_p`, so the distinguished place
  is Harris's `v ∈ Φ_p`.

The module also gives Harris's decomposition
`𝒟_p = ∏_j 𝒟_j × ∏_j c(𝒟_j)` of `ℚ_p ⊗[ℚ] A` over the places of `K` above `p`.

## Source

Harris (1999), Section 4, printed pp. 308-309 (PDF pp. 10-11): "We assume `p`
splits in `𝒦₀`. We fix a prime `v = v^(1) ∈ S(ℬ)` of residue characteristic
`p` … The CM type `Φ` corresponds to a set of primes `Φ_p` of `𝒦` above `p`,
via the identification `𝒦 ≅ E(GG, X_{n-1})` (cf. [H1]), and we assume
`v ∈ Φ_p`. Let `Φ_p = {v^(j), j = 1, …, t}`, and write
`𝒟_p = ∏_{j=1}^t 𝒟_j × ∏_{j=1}^t c(𝒟_j)`; here `𝒟_j = 𝒟 ⊗ 𝒦_{v^(j)}` and `c`
denotes complex conjugation." Then (4.1): `K_p = C_v × ∏_{j>1} C^(j) × ℤ_pˣ`,
(4.2): `GJ_p ≅ ∏_j (𝒟_j)ˣ × ℚ_pˣ`, and
"`K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ`".

Harris (1997), Section 2, printed pp. 88-89 (PDF pp. 14-15): `𝒦₀` "is an
imaginary quadratic field in which `p` splits as the product `𝔭₁ · 𝔭₂`", and
"Let `Φ` be the set of embeddings `η: 𝒦 ↪ Q̄` such that `φ ∘ η` induces the
prime `𝔭₁` of `𝒦₀`."

## Declarations

All declarations are in namespace `Langlands.Shimura`.

### The place of `ℚ` at `p`

- `rationalPrimePlace p`, for a prime `p`, is the finite place of `ℚ` at `p`:
  the image of `p` under Mathlib's `Rat.HeightOneSpectrum.primesEquiv.symm`.
  This is the place at which Mathlib identifies `ℚ_v` with `ℚ_p`.
- `natCast_mem_rationalPrimePlace`: it contains `p`.
  `eq_rationalPrimePlace`: it is the only finite place of `ℚ` containing `p`.
- `liesOver_rationalPrimePlace_iff`: for a number field `K`, a finite place
  `w` of `K` lies over `rationalPrimePlace p` exactly when `p ∈ w`.

### Harris's place `u`

Fix `θ : ℂ →+* PadicAlgCl p` as in `HarrisCMTypePrimes`.

- `harrisPrime_liesOver_rationalPrimePlace` (an instance): every
  `harrisPrime p θ φ` lies over `rationalPrimePlace p`.
- `harrisPlace p θ τ`, for `τ : F →+* ℂ`, is `u = harrisPrime p θ τ` as an
  element of `FinitePlacesAbove F (rationalPrimePlace p)` (`harrisPlace_val`).

Let `F` be imaginary quadratic (`[IsCMField F]`,
`[Algebra.IsQuadraticExtension ℚ F]`).

- `card_finitePlacesAbove_eq_two_iff`: `F` has exactly two places above `p`
  (`p` splits) if and only if `u ≠ ū`.
- `harrisPlace_bijective`: if `u ≠ ū`, the completion map `ℚ_p → F_u` is
  bijective. This is the hypothesis `h𝔭` of the published split-prime units,
  obtained from the published `completionMap_bijective_of_split`.
- `cmTypePrimesEquiv p θ ι τ`, for `ι : F →+* K` with `K` a CM field, is the
  bijection between `Φ_p` for Harris's type
  `Φ = CMType.inducedFromImaginaryQuadratic ι τ` and
  `FinitePlacesAbove K u` (with `K` an `F`-algebra through `ι`). Both sides are
  subtypes of the finite places of `K`, and the map is the identity on places
  (`cmTypePrimesEquiv_val`). It comes from
  `cmTypePrimes_inducedFromImaginaryQuadratic`.

### Decomposition over `Φ_p`

Let `K` be a CM field and `Φ` a CM type of `K`.

- `not_mem_cmTypePrimes_iff`: if `Φ_p` is disjoint from the set of
  `Φ.conjugate`, a place of `K` above `p` lies outside `Φ_p` if and only if it
  lies in the set of `Φ.conjugate`.
- `not_mem_cmTypePrimes_inducedFromImaginaryQuadratic_iff`: for Harris's type
  and `u ≠ ū`, a place above `p` lies outside `Φ_p` if and only if it is a
  complex conjugate `c(w)` of a place `w ∈ Φ_p` (`conjPrime`).
- `cmTypeTensorEquiv p θ A Φ`, for a `K`-algebra `A` with `ℚ → K → A`, is the
  ring isomorphism
  `ℚ_p ⊗[ℚ] A ≃ (Π_{w ∣ p, w ∈ Φ_p} K_w ⊗[K] A) × (Π_{w ∣ p, w ∉ Φ_p} K_w ⊗[K] A)`.
  It is the published `PlaceTensor.placeTensorEquiv` at the place of `ℚ` at
  `p`, followed by splitting the product along `Φ_p` (Mathlib's
  `RingEquiv.piEquivPiSubtypeProd`). On pure tensors both components are
  `x ⊗ a ↦ (x ⊗ a)_w` (`cmTypeTensorEquiv_tmul_fst`,
  `cmTypeTensorEquiv_tmul_snd`). For `A = 𝒟`, Harris's type and `u ≠ ū`, the
  first factor is `∏_j 𝒟_j` and, by the previous result, the second is
  `∏_j c(𝒟_j)`.

### Harris's group and level at his data

In the setting of `HarrisSplitPrimeFactors` and `HarrisDivisionLevels`, let
`σ : SecondKindInvolution E K A`, with `K` a CM field, `A` finite over `ℚ` and
`ι : F →+* K`. Assume `u ≠ ū` (`hsplit`).

- `σ.harrisCMPoints p θ ι τ hsplit` is the published `σ.splitPlacePoints` at
  `v = rationalPrimePlace p` and `𝔭 = harrisPlace p θ τ`:
  `GG(ℚ_p) ≃ Π_{w ∣ u} (K_w ⊗[K] A)ˣ × ℚ_pˣ`. Here the index set
  `FinitePlacesAbove K u` is `Φ_p` by `cmTypePrimesEquiv`.
- `σ.harrisCMLevel p θ ι τ hsplit hdiv v₀ r hr0 hr` is the published
  `σ.harrisLevel` at the same data, for `hdiv` the division hypothesis at the
  places above `u`, a distinguished place `v₀ ∈ Φ_p` (Harris's `v ∈ Φ_p`), and
  a radius `0 < r < 1`. It is Harris's
  `K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ` when `r = ‖ϖ‖^N` for a
  uniformizer `ϖ` of `K_{v₀}`.
- `mem_harrisCMLevel`: `g ∈ K(N)_p` if and only if:
  - the `v₀`-component of `harrisCMPoints g` lies in the congruence level;
  - every other component lies in the maximal compact level;
  - the multiplier lies in `ℤ_pˣ`.

## Scope

- **Inputs, not proved:** the division hypothesis `hdiv`, and Harris's
  further assumptions on the algebra at `v` (`inv_v(ℬ) = 1/n`) and on `𝒟`.
- **Group side:** the group is the published `GG` of the second-kind
  involution `σ` on `A`. For Harris's `GJ`, apply the same definitions to the
  algebra `𝒟` with its involution.
- **Decomposition:** `cmTypeTensorEquiv` decomposes the algebra
  `ℚ_p ⊗[ℚ] A`. It is not shown to be compatible with the involution, which
  exchanges the two factors.

## Provenance

Derived from Harris (1999), Section 4, printed pp. 308-309, and Harris (1997),
Section 2, printed pp. 88-89, both read in the original. These definitions are
specializations of the published split-prime units and of
`HarrisCMTypePrimes` to Harris's data. Using Mathlib's `primesEquiv` for the
place at `p` and splitting the place decomposition along `Φ_p` are
implementation choices.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-1997-drinfeld-cohomology`:
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.

Formal dependencies: `Langlands.Shimura.Unitary.HarrisCMTypePrimes`
(candidate `7c3ffd3c-a1e6-461f-ad26-ac7feb760906`, staged), the published
`Langlands.Shimura.Unitary.HarrisDivisionLevels` and through it
`HarrisSplitPrimeFactors` and `PlaceTensorDecomposition`, and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0. The Mathlib
results used include `Rat.HeightOneSpectrum.primesEquiv`,
`RingEquiv.piEquivPiSubtypeProd` and `Nat.card_congr`.
