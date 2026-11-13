# A Galois-stable chamber with an Iwahori model over the maximal unramified extension

This module states `LocalSimplyConnectedUnramifiedChamberStatement`, the
building input of the proofs of Kaletha–Prasad Theorems 10.6.1 and 10.6.4 for a
semisimple simply connected group over a nonarchimedean local field. It is
stated with the Library's supplied building data over the maximal unramified
extension. The reduction module `LocalUnramifiedChamberReduction` derives from
it the interface statement `LocalSimplyConnectedUnramifiedIntegralTwistStatement`.

## Statement

Let `F` be a nonarchimedean local field (`IsNonarchimedeanLocalField F`, at
universe `u`) and let `L = LocalGalois.Separable.inertiaFixedField F`, the
maximal unramified extension of `F` inside its separable closure. Write
`Γ = Gal(L/F)` (`L ≃ₐ[F] L`) and `G_L = baseChanged F L G`. Let `G` be an affine
group scheme over `Spec F` (`IsAffineHom G.X.hom`) with `IsSimplyConnected G`.

The proposition asserts that there exist

- building data `C : MaximalUnramified.BuildingData F G_L` for `G_L` (an
  `IntegerValuationBuildingData` for the valuation of `L`), with reduced
  building `C.ReducedBuilding` and its action of `G(L) = rationalPoints G_L`
  by `g • y`;
- semilinear Galois data `D : MaximalUnramified.SemilinearApartmentData C`,
  whose action `D.action σ` of `σ ∈ Γ` on `C.ReducedBuilding` satisfies
  `D.action σ (g • y) = σ(g) • D.action σ y` (`action_smul`, with
  `σ(g) = rationalConjugate F L G σ g`);
- an integral model `M : IntegralModel 𝒪[F] F G`;
- a subset `Y₀ ⊆ C.ReducedBuilding`,

such that

1. `M` is smooth over `𝒪[F]` (`M.IsSmooth`);
2. the special fibre of `M.group`, its base change along
   `Spec 𝓀[F] → Spec 𝒪[F]`, has a connected underlying space;
3. `Y₀` is a chamber (`C.IsChamber Y₀`);
4. `Y₀` is `Γ`-stable: `D.action σ '' Y₀ = Y₀` for every `σ ∈ Γ`;
5. the image in `G(L)` of the integral points of `M` over the valuation ring of
   `L` is the stabilizer of `Y₀`: for every `g ∈ G(L)`,
   `g ∈ M.baseChangeUnramified.integralPoints` if and only if
   `(g • ·) '' Y₀ = Y₀`. Here `M.baseChangeUnramified` is the base change of `M`
   to `fixedFieldIntegers F`, the valuation ring of `L`, and `integralPoints`
   is the range of its integral points in the rational points of `G_L`;
6. `G(L)` acts transitively on chambers: every chamber `Y` equals
   `(g • ·) '' Y₀` for some `g ∈ G(L)`;
7. for every map `c : Γ → G(L)` that is a crossed homomorphism,
   `c (σ * τ) = c σ * σ(c τ)`, and is trivial on the fixing subgroup of some
   finite-dimensional intermediate field `E` of `L/F`, some chamber `Y` is
   stable under the twisted action: `(fun y => c σ • D.action σ y) '' Y = Y`
   for every `σ ∈ Γ`.

Item 4 together with item 5 says that `M` is the Iwahori model of the
`Γ`-stable chamber `Y₀`, whose `𝒪_L`-points form the Iwahori subgroup, and that
this subgroup is the full stabilizer of `Y₀` because `G` is simply connected.

## Source

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), with `k = F`,
`K = L`, `Γ = Gal(K/k)`, `O` the valuation ring of `K` and `o` that of `k`:

- Items 3, 4, 1, 2 and the `o`-model: Proposition 9.10.4 and Proposition 9.10.1
  (printed pp. 381–382, PDF pp. 412–413): since the residue field of `F` is
  finite, `G` is residually quasi-split, so `B(G_K)` contains a `Γ`-stable
  chamber `C`. By 9.2.5 (printed pp. 327–328, PDF pp. 358–359), for a
  `Γ`-stable bounded subset the connected Bruhat–Tits group scheme `G_C^0`
  descends to a smooth affine `o`-group scheme with generic fibre `G` and
  connected special fibre; 9.2.6 (printed p. 329, PDF p. 360) calls `G_C^0(O)`
  the Iwahori subgroup.
- Item 5: by Axiom 4.1.9 and 4.1.12(1) (printed p. 161, PDF p. 192), the
  connected parahoric subgroup `G(K)_C^0` is the stabilizer and the pointwise
  stabilizer of `C` in `G(K)^0`, and `G(K)^0 = G(K)` for simply connected `G`
  (Remark 4.1.13, same page; 9.3.26, printed p. 344, PDF p. 375). So the
  stabilizer of `C` in `G(K)` is `G_C^0(O)`. Theorem 10.6.4 (printed p. 399,
  PDF p. 430) uses this in the form that the Iwahori subgroup is its own
  normalizer.
- Item 6: 4.1.12(4) (printed p. 161, PDF p. 192): `G(K)` acts transitively on
  pairs of an apartment of `B(G_K)` and a chamber in it (compare Proposition
  9.3.22, printed p. 342, PDF p. 373, for the descended building).
- Item 7: proof of Theorem 10.6.1 (printed pp. 397–398, PDF pp. 428–429): for
  a cocycle `c` of `Γ` in `G(K)`, Proposition 9.10.4 applied to the twisted
  group `_cG` gives a chamber of `B(G_K)` stable under the twisted action
  `x ↦ c(γ) γ(x)`. The finiteness hypothesis on `c` expresses that the cocycle
  is continuous for the profinite topology on `Γ`, so that `_cG` is a
  `k`-form of `G`.

## Provenance

This is a derived statement, not a numbered result of the source. It collects
the building facts used in the proofs of KP Theorems 10.6.1 and 10.6.4 for the
building of `G_K`, in the Library's language of supplied building data
(`MaximalUnramified.BuildingData`, `IntegerValuationBuildingData.IsChamber`)
and semilinear Galois data (`MaximalUnramified.SemilinearApartmentData`). The
Library does not yet construct the building of `G_K` or its Bruhat–Tits group
schemes, so the building data, the Galois data and the model are asserted to
exist together with the listed properties; the statement does not assert that
these data are the Bruhat–Tits building. Nothing in this module is proved.
