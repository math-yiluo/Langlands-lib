# Kottwitz's good primes: standard unramified charts and hyperspecial levels

Author: Worker 8. Module `Langlands.Shimura.Unitary.KottwitzChart`, namespace
`Langlands.Shimura.KottwitzUnramified`.

This module states Kottwitz's conditions (a) and (b) at a rational prime for the
Library's unitary similitude group of a central simple algebra with an involution
of the second kind. The conditions are formulated concretely, through matrix charts
of `ℚ_p ⊗_ℚ A` over the completions of the CM field, in which the involution has a
standard antidiagonal form and the level is the group of integral points. The last
section explains how these concrete conditions agree with the general notions
"quasi-split and split over an unramified extension" and "hyperspecial".

## Source

Kottwitz, *On the λ-adic representations associated to some simple Shimura
varieties*, Invent. Math. 108 (1992), §1, printed pp.655-656 (PDF pp.3-4),
source `kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`. Kottwitz fixes a
finite set `S_bad` of primes such that for every prime `p ∉ S_bad`:

> (a) the group `G` is quasi-split over `ℚ_p` and split over an unramified extension
> of `ℚ_p`;
> (b) the compact open subgroup `K` of `G(𝔸_f)` is a product `K^p K_p`, where `K^p`
> is a compact open subgroup of `G(𝔸_f^p)` and `K_p` is a hyperspecial maximal
> compact subgroup of `G(ℚ_p)`;
> (c) the function `f_∞` can be written as the product of a function `f^p` in the
> Hecke algebra of `G(𝔸_f^p)` with respect to `K^p` times the unit element of the
> Hecke algebra of `G(ℚ_p)` with respect to `K_p`.

Here, as on printed p.654, `G(R) = {x ∈ D ⊗_ℚ R : x x* ∈ R^×}`. This module treats
(a) and (b). Condition (c) concerns the Hecke projector `f_∞` of the cohomology and
belongs to the cohomological statement of Kottwitz's Theorem 1, not to this module.

Supporting sources for the comparison with the general notions:

- Tits, *Reductive groups over local fields*, Corvallis I (1979), source
  `tits-1979-reductive-groups-local-fields`, SHA-256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`: §3.8.1
  (printed p.55, PDF p.59), hyperspecial subgroups are exactly the groups of
  integral points of smooth group schemes over the integers with generic fibre `G`
  and reductive special fibre; §1.10 and §3.8.2, such subgroups exist when `G` is
  quasi-split with an unramified splitting field.
- Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer. Math.
  Soc. 5 (1992), source `kottwitz-1992-points-shimura-finite-fields`: §5 (printed
  p.389) and §7 (printed pp.395-396, Lemma 7.2 and Corollary 7.3). For unramified PEL
  data the algebra over `ℚ_p` is a product of matrix algebras over unramified
  extensions, there is a `*`-stable maximal order, and the hyperspecial level is the
  stabilizer of a self-dual lattice; such lattices form one orbit.

## Notation

The Library's notation differs from Kottwitz's: `E` is the totally real field
(Kottwitz's `F₀`), `K` the CM field (Kottwitz's `F`), and `A` the algebra (Kottwitz's
`D`). The involution is `σ : SecondKindInvolution E K A`, or the underlying involution
of `σ : CentralSimpleUnitaryData E K A n`; `σ.rationalInvolution` is its restriction of
scalars to `ℚ`. The place `p : HeightOneSpectrum (𝓞 ℚ)` is a finite place of `ℚ`, with
completion `ℚ_p = p.adicCompletion ℚ`. The places of `K` above it are the published
`FinitePlacesAbove K p`; for such a `w`, `K_w = w.1.adicCompletion K` and
`O_w = w.1.adicCompletionIntegers K`. The local group
`LocalPoints σ p = σ.rationalInvolution.Points ℚ_p` is the published group of pairs
`(g, c)` with `g ∈ (ℚ_p ⊗_ℚ A)ˣ`, `c ∈ ℚ_pˣ` and `g σ(g) = c`: this is Kottwitz's
`G(ℚ_p)`.

## Declarations

### Places

- `integerConjugation E K : 𝓞 K ≃+* 𝓞 K` is the published CM conjugation
  `cmConjugation E K` restricted to the ring of integers (Mathlib's
  `RingOfIntegers.mapRingEquiv`). `integerConjugation_algebraMap`: it fixes the image
  of `𝓞 ℚ` (both maps send an integer to itself). `integerConjugation_involutive`: it
  is an involution.
- `placeConj p w` is the conjugate place `w̄ = c⁻¹(w)`, the prime ideal
  `{x : c(x) ∈ w}` of `𝓞 K` (Mathlib's `HeightOneSpectrum.comap`). It lies over `p`
  because `c` fixes `𝓞 ℚ`. `mem_placeConj` unfolds membership and
  `placeConj_placeConj` proves `w̄̄ = w`. A place of `E` below `w` is split in `K` when
  `w̄ ≠ w` and inert or ramified when `w̄ = w`.
- `IsUnramifiedAt p K`: every place `w` of `K` above `p` has Mathlib ramification
  index `w.1.asIdeal.ramificationIdx (𝓞 ℚ) = 1`.

### Charts

Assume `[Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]`; the last is needed
by the published decomposition.

- `MatrixProduct K p n` is `Π_{w ∣ p} M_n(K_w)`.
- `PlaceCharts K A p n` is a family of `K_w`-algebra isomorphisms
  `K_w ⊗_K A ≃ M_n(K_w)`, one for each place `w` above `p`. Being `K_w`-linear, each
  sends the centre `K_w` to the scalar matrices.
- `chartEquiv φ : ℚ_p ⊗_ℚ A ≃+* Π_w M_n(K_w)` is the published decomposition
  `PlaceTensor.placeTensorEquiv p A : ℚ_p ⊗_ℚ A ≃ Π_{w ∣ p} K_w ⊗_K A`, followed by the
  charts.
- `transportedInvolution σ φ x` is `Ψ (σ_{ℚ_p} (Ψ⁻¹ x))`, where `Ψ = chartEquiv φ` and
  `σ_{ℚ_p} = σ.rationalInvolution.baseChange ℚ_p` is the involution `σ ⊗ 1` of
  `ℚ_p ⊗_ℚ A` used to define the published points.
- `UnramifiedChart σ p n` is a *standard unramified chart*. It consists of charts
  `φ` together with ring homomorphisms `c_w : K_{w̄} → K_w` (field `conj`) that carry
  `O_{w̄}` into `O_w` (field `conj_integer`), such that for all `x`, `w`, `k`, `l`
  (field `involution_eq`)

  `θ(x)_w k l = c_w (x_{w̄} (rev l) (rev k))`, where `θ = transportedInvolution σ φ`,

  that is, `θ(x)_w = J · c_w(x_{w̄})ᵀ · J` with `J` the antidiagonal matrix of ones
  and `c_w` applied entrywise. The maps `c_w` are determined by `θ`: applied to the
  scalar matrices of `K`, the identity says that `c_w` extends the CM conjugation, so
  it is the completion of `c` at `w̄`. The structure stores charts only; it stores no
  representation, parameter or polynomial.

### Points and levels

- `pointUnit φ : LocalPoints σ p →* (Π_w M_n(K_w))ˣ` sends `(g, c)` to `Ψ(g)`
  (`pointUnit_val`).
- `integralMatrices K p n` is the subring `Π_w M_n(O_w)`; `mem_integralMatrices`
  unfolds membership. The subring axioms are proved from the valuation-subring
  structure of `O_w` (sums of products for matrix multiplication).
- `UnramifiedChart.level c` is the subgroup of points `g` with `Ψ(g)` and `Ψ(g)⁻¹`
  integral, that is, `Ψ(g) ∈ Π_w GL_n(O_w)` (Mathlib's `Submonoid.units`, pulled
  back along `pointUnit`). `mem_level` unfolds membership. No condition on the
  multiplier is imposed: if `g` and `g⁻¹` are integral then `c = g σ(g)` and `c⁻¹`
  are integral, because the chart condition makes the order `Ψ⁻¹(Π M_n(O_w))`
  stable under `σ`, so `c ∈ ℤ_pˣ` automatically.

### Kottwitz's conditions

Now `σ : CentralSimpleUnitaryData E K A n`, with matrix size the given `n`.

- `IsKottwitzUnramifiedAt σ p`, condition (a): `IsUnramifiedAt p K` and a standard
  unramified chart exists.
- `IsHyperspecialLevel σ p Kp`, condition (b) for a subgroup `Kp` of `G(ℚ_p)`: `K` is
  unramified at `p` and `Kp` is the level of some standard unramified chart.
  `IsHyperspecialLevel.isKottwitzUnramifiedAt`: (b) implies (a).
- `IsKottwitzGoodPrime σ Kf ℓ hℓ`, for `[Module.Finite ℚ A]`, a subgroup `Kf` of the
  published finite adelic points and a rational prime `ℓ`: at the place `v` of `ℚ`
  whose ideal contains `ℓ`, condition (a) holds, and under the published splitting
  `finiteAdelicPointsSplit ℓ : G(𝔸_f) ≃ G(Π_{v ∣ ℓ} ℚ_v) × G(𝔸_f^ℓ)` the image of
  `Kf` is a product `K_ℓ × K^ℓ` in which `K_ℓ`, read in `G(ℚ_v)` through the published
  isomorphism `dividingLocalMap ℓ v`, is a hyperspecial level. This is Kottwitz's
  (a) together with (b). Compactness and openness of `Kf` are hypotheses of
  Kottwitz's setting, carried by the consumer's level type, and are not repeated.

## Agreement with the general notions

This section explains why the concrete conditions are Kottwitz's. These
arguments are standard and are not formalized here.

*From a chart to (a) and (b).* Let `c` be a standard unramified chart at a place
where `K` is unramified. Then each `K_w` is unramified over `ℚ_p`, and
`𝒪 = Ψ⁻¹(Π_w M_n(O_w))` is a `ℤ_p`-order, stable under `σ` because the maps `c_w`
preserve integers. The functor `R ↦ {(g, t) ∈ (𝒪 ⊗ R)ˣ × Rˣ : g σ(g) = t}` is a
smooth affine group scheme over `ℤ_p` with generic fibre `G_{ℚ_p}`. At a pair of
places `w ≠ w̄` its points are `GL_n(O_w ⊗ R) × Rˣ` (the `w̄`-component is determined
by the `w`-component and the multiplier). At a place `w = w̄`, which is inert because
`K` is unramified at `p`, it is the unitary similitude group of the unimodular
Hermitian form given by `J` over the unramified quadratic extension `O_w` of the
integers of `E_v`. All fibres are connected reductive, so this is a reductive model,
and by Tits §3.8.1 its group of integral points `c.level` is a hyperspecial
subgroup. The upper triangular matrices form a Borel subgroup over `ℚ_p`, because
`θ` preserves upper triangular matrices, so `G` is quasi-split, and it splits over
the unramified extension that splits every `K_w`.

*From (a) and (b) to a chart.* Conversely, suppose that (a) and (b) hold. The centre
of `G` contains the torus `{z ∈ Res_{K/ℚ} 𝔾_m : z z̄ ∈ 𝔾_m}`, whose splitting over an
unramified extension forces `K` to be unramified at `p`. By Tits §3.8.1, `K_p` is the
group of integral points of a reductive model. For these PEL groups this model is
given by a `σ`-stable maximal order, which is a product of matrix algebras over the
`O_w` (Kottwitz 1992 JAMS, §5 and §7). A `σ`-stable maximal order at a pair `w ≠ w̄`
gives the antidiagonal normal form after a change of chart at `w̄`. At an inert place
it gives a unimodular Hermitian form over the unramified extension. All such forms
are isometric to the antidiagonal form `J` (Kottwitz 1992 JAMS, Lemma 7.2). Hence
`K_p` is the level of a standard unramified chart.

## Scope and provenance

The formulation through charts in antidiagonal normal form is a derived, concrete
presentation of Kottwitz's conditions for these groups. The derivation is the
argument above. The module proves no comparison with abstract reductive group
schemes, buildings or hyperspecial vertices, which the Library does not provide in a
form applicable to these groups. It does not prove that `c.level` is compact, open or
maximal compact, or that charts exist. It assumes no Satake or Langlands
correspondence. The torus, Borel subgroup and unramified principal series attached
to a chart are constructed in the companion modules.

Formal dependencies: `Langlands.Shimura.Unitary.CMData` (`cmConjugation`,
`SecondKindInvolution`, `CentralSimpleUnitaryData`), `Unitary.Adelic` (`Points`),
`Unitary.PlaceTensorDecomposition` (`placeTensorEquiv`), `Unitary.PointsSplit`
(`finiteAdelicPointsSplit`, `dividingLocalMap`, `PrimeToPoints`), and
`Global.AdelicFunctoriality` (`FinitePlacesAbove`). Environment: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
