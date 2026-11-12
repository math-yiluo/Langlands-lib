# Harris's similitude group at a split prime as a product over places

Author: Worker 19.

This module completes the identification of Harris (1999), (4.2), and Harris
(1998), (A.1), for the unitary similitude group of the published Harris
setting: at a degree-one place `𝔭` of the imaginary quadratic field `F` above
the rational place `v`,

`GG(ℚ_v) ≃* Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ × ℚ_vˣ`,

where `w` runs over the places of the CM field `K` above `𝔭`. It combines the
published `HarrisSplitPrimePoints` (`GG(ℚ_v) ≃* (ℚ_v ⊗[F, u] A)ˣ × ℚ_vˣ`)
with the decomposition `PlaceTensorDecomposition` submitted together with
this module.

## Source

Harris (1998), Appendix, printed p. 206 (PDF p. 30): for `GG = GU(B, α)`, `B`
a division algebra over the CM field `E = E₀ · K₀` with involution of the
second kind, and `p = 𝔭₁ · 𝔭₂` split in the imaginary quadratic field `K₀`,
the places of `E` over `𝔭_i` are `v_i^(j)`, `j = 1, …, s`, `F_j` is the
completion of `E` at `v_i^(j)`, and

"(A.1) `GG(ℚ_p) ≅ ∏_j B(F_j)ˣ × ℚ_pˣ`".

Harris (1999), Section 4, printed pp. 308-309 (PDF pp. 10-11): with `p` split
in `𝒦₀`, the CM type `Φ` "corresponds to a set of primes `Φ_p` of `𝒦` above
`p`"; writing `Φ_p = {v^(j), j = 1, …, t}`, `𝒟_p = ∏_j 𝒟_j × ∏_j c(𝒟_j)`
with `𝒟_j = 𝒟 ⊗ 𝒦_{v^(j)}`, Harris identifies "(4.2) `GJ_p ≅ ∏_j (𝒟_j)ˣ × ℚ_pˣ`
as in [H2, Appendix, A.1]".

Correspondence: Harris's `K₀` or `𝒦₀` is `F`, the CM field `E` or `𝒦` is
`K`, the totally real field is `E` here, the algebra `B` or `𝒟` with its
involution is `A` with `σ : SecondKindInvolution E K A`, and Harris's prime
`𝔭_i` of `K₀` is the place `𝔭` of `F`. The places `v^(j)` of `K` above it are
`FinitePlacesAbove K 𝔭`, and `𝒟_j = 𝒟 ⊗_𝒦 𝒦_{v^(j)}` is `K_w ⊗[K] A`. The
places of `Φ_p` in Harris (1999) lie above one prime of `𝒦₀`, the one
determined by the chosen complex embedding of `𝒦₀` and an identification of
`ℂ` with an algebraic closure of `ℚ_p`; this module takes the place `𝔭` as
input and does not formalize that choice.

## Declarations

All declarations are in namespace `Langlands.Shimura`.

### A degree-one place

For a number field `F`, a finite place `v` of `ℚ`, `𝔭 : FinitePlacesAbove F v`
and `h𝔭`, the bijectivity of the published completion map
`FiniteExtension.completionMap v 𝔭 : ℚ_v → F_𝔭`:

- `splitPlaceEquiv v 𝔭 h𝔭 : ℚ_v ≃+* F_𝔭` is this bijection
  (`splitPlaceEquiv_apply`).
- `splitPlaceEmbedding v 𝔭 h𝔭 : F →+* ℚ_v` is `F → F_𝔭` followed by its
  inverse: the embedding `u` of `HarrisSplitPrimePoints` attached to `𝔭`.
- `splitPlaceAlgEquiv v 𝔭 h𝔭` is `splitPlaceEquiv` as an isomorphism of
  `F`-algebras, for `ℚ_v` an `F`-algebra through `splitPlaceEmbedding`.
- `completionMap_bijective_of_split v hsplit 𝔭`: if `F` is quadratic over `ℚ`
  and has exactly two places above `v` (`p` splits in `F`), then `h𝔭` holds
  for every `𝔭` above `v`. This is
  `PlaceTensor.completionMap_bijective_of_le_card` with `[F : ℚ] = 2`.

### The Harris setting

As in `HarrisSplitPrimePoints`: `E` totally real, `K` a totally complex
quadratic extension of `E`, `F` a CM field with `ι : F →+* K`, `A` a
`K`-algebra; `ι.toAlgebra` makes `K` an `F`-algebra and
`imaginaryQuadraticAlgebra ι` makes `A` one.

- `imaginaryQuadraticAlgebra_isScalarTower ι`: with these structures,
  `F → K → A` is a scalar tower (by definition of the structure on `A`).
- `splitPlaceFactorEquiv A ι v 𝔭 h𝔭 : ℚ_v ⊗[F] A ≃+* Π_{w ∣ 𝔭} K_w ⊗[K] A`,
  for `ℚ_v` an `F`-algebra through `splitPlaceEmbedding`, is the base change of
  `splitPlaceAlgEquiv` followed by `PlaceTensor.placeTensorEquiv 𝔭 A`.
  `splitPlaceFactorEquiv_tmul`: `s ⊗ a ↦ (completionMap 𝔭 w (completionMap v 𝔭 s) ⊗ a)_w`.

Assume moreover that `F` is quadratic over `ℚ`, and let
`σ : SecondKindInvolution E K A` with the published rational structure.

- `σ.splitPlacePoints ι v 𝔭 h𝔭 :
  σ.rationalInvolution.Points ℚ_v ≃* (Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ) × ℚ_vˣ` is the
  published `σ.splitPrimePoints ι v (splitPlaceEmbedding v 𝔭 h𝔭)` followed by
  the isomorphism of unit groups induced by `splitPlaceFactorEquiv` and
  `MulEquiv.piUnits`, and the identity on `ℚ_vˣ`.
- `splitPlacePoints_fst` and `splitPlacePoints_snd` state, by `rfl`, that the
  `w`-component of the first coordinate of a point is the `w`-component of
  `splitPlaceFactorEquiv` applied to the image of its algebra unit under
  `ImaginaryQuadraticSplit.projection` (`s ⊗ a ↦ s ⊗ a` from `ℚ_v ⊗[ℚ] A` to
  `ℚ_v ⊗[F] A`), and that the second coordinate is the multiplier.

## Scope

Only the group isomorphism is constructed; topologies, the level subgroups
`C_v × ∏_{j>1} C^(j) × ℤ_pˣ` of (4.1) in this product form, and the
comparison of the two inner forms `GG` and `GJ` are not treated. Harris's
hypotheses that `A` is central simple, a division algebra, and has invariant
`1/n` at the distinguished place are not used. The construction applies to
any place `𝔭` whose completion map is bijective; Harris's choice of `𝔭`
through the CM type is not formalized.

## Provenance

Derived from Harris (1998), Appendix, (A.1) on printed p. 206, and Harris
(1999), Section 4, (4.2) on printed p. 309, both read in the original. The
use of the completed tensor comparison for the decomposition over places, the
degree-one criterion for split primes and the explicit coordinate maps are
implementation choices.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-1998-local-langlands`:
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

Formal dependencies: `Langlands.Shimura.Unitary.PlaceTensorDecomposition`,
the published `Langlands.Shimura.Unitary.HarrisSplitPrimePoints` (with
`ImaginaryQuadraticSplitPoints` and `CMData`), the published
`Langlands.Global.AdelicFunctoriality` completion maps, and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`RingEquiv.ofBijective`, `AlgEquiv.ofRingEquiv`, `Algebra.TensorProduct.congr`,
`Units.mapEquiv`, `MulEquiv.piUnits` and `MulEquiv.prodCongr`.
