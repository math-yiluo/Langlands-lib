# Twisting unramified simply connected cocycles into an Iwahori model

This module states `LocalSimplyConnectedUnramifiedIntegralTwistStatement`, the
building-theoretic step in the proof that unramified Galois cohomology of a
semisimple simply connected group over a nonarchimedean local field vanishes.
It is an interface between two parts of that proof: the building part, which
produces the twisting point, and the cohomological part, which concludes with
Lang's theorem for a smooth model with connected special fibre.

## Statement

Let `F` be a nonarchimedean local field (`IsNonarchimedeanLocalField F`, at
universe `u`) and let `L = LocalGalois.Separable.inertiaFixedField F`, the fixed
field of the inertia subgroup in `SeparableClosure F`, that is, the maximal
unramified extension of `F` inside its separable closure. Let `G` be an affine
group scheme over `Spec F` with `IsSimplyConnected G`.

The proposition asserts that there is an integral model
`M : IntegralModel 𝒪[F] F G` such that

1. `M` is smooth over `𝒪[F]` (`M.IsSmooth`);
2. the special fibre of `M.group`, its base change along
   `Spec 𝓀[F] → Spec 𝒪[F]`, has a connected underlying space;
3. for every field `E` that is a finite Galois extension of `F` and comes
   with an `F`-embedding into `L` (`Algebra E L`, `IsScalarTower F E L`), and
   every crossed homomorphism `c : Gal(E/F) → G(E)`, meaning
   `c (σ * τ) = c σ * σ(c τ)` with `σ(-)` the coefficient action
   `GaloisPoint.conjugate F E G σ`, there is a point `h ∈ G(L)` such that for
   every `σ ∈ Gal(L/F)` the point

   `h⁻¹ * relativeExtend (c (σ|E)) * σ(h)`

   has integral coordinates for `M` (`M.HasIntegralCoordinates L`): every
   regular function of the model takes a value at it that is integral over
   `𝒪[F]`. Here `σ|E = σ.restrictNormal E`, `relativeExtend` is
   `GaloisPoint.relativeExtend F E L G`, the map `G(E) → G(L)` induced by the
   embedding, and `σ(h) = GaloisPoint.conjugate F L G σ h`.

The model `M` is chosen once, before the extension `E` and the cocycle `c`.
Since `L/F` is algebraic and unramified, the elements of `L` integral over
`𝒪[F]` form the valuation ring of `L`, so condition 3 says that the twisted
cocycle `σ ↦ h⁻¹ c(σ|E) σ(h)` takes values in the `𝒪_L`-points of `M`.

## Source

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), with `k = F`,
`K = L`, `Γ = Gal(K/k)`, `O` the valuation ring of `K` and `o` that of `k`:

- Theorem 10.6.1 (printed p. 397, PDF p. 428), proof of the surjectivity of
  `H¹(Γ, N) → H¹(Γ, G(K))`: for a cocycle `c` of `Γ` in `G(K)`, Proposition 9.10.4
  applied to the twisted group `_cG` gives a chamber `C'` of `B(G_K)` stable
  under the twisted action `x ↦ c(γ)γ(x)`; chambers of `B(G_K)` are conjugate
  under `G(K)`, so `C' = g · C` for the chosen `Γ`-stable chamber `C` and some
  `g ∈ G(K)`, and then `g⁻¹ c(γ) γ(g)` normalizes the Iwahori subgroup
  `I = G_C^0(O)`.
- Theorem 10.6.4 (printed p. 399, PDF p. 430): for simply connected `G`, every
  Iwahori subgroup of `G(K)` is its own normalizer (Proposition 1.4.5(3) and
  Axiom 4.1.9), so `g⁻¹ c(γ) γ(g) ∈ I`.
- Proposition 9.10.4 and Proposition 9.10.1 (printed pp. 381–382, PDF
  pp. 412–413): since the residue field of `F` is finite, `G` is residually
  quasi-split, so a `Γ`-invariant `K`-chamber `C` exists. Its Iwahori group
  scheme `G_C^0` is a smooth affine group scheme with connected fibres; as `C`
  is `Γ`-stable it is defined over `o` (unramified descent, KP Chapter 9),
  and `G_C^0(O) = I`. This gives the model `M` of items 1 and 2.

In the source the twisting element `g` is an element of `G(K)`; the statement
keeps it at the level of the infinite field `L` and lets the cocycle come from
any finite Galois subextension, so that the conclusion is exactly the output
of this argument. The step from it to the vanishing of the cocycle (descent of
`g` to a finite level and Lang's theorem, KP Lemma 8.1.4, which is published as
`localUnramifiedIntegralCocycleVanishing`) is not part of this statement.

## Provenance

This is a derived interface statement, not a numbered result of the source.
It packages the building part of the proofs of KP Theorems 10.6.1 and 10.6.4
for semisimple simply connected groups over a nonarchimedean local field,
expressed with the Library's `IntegralModel.HasIntegralCoordinates`, the
coefficient action `GaloisPoint.conjugate` and the coefficient extension
`GaloisPoint.relativeExtend`. It is introduced to split the proof of
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement` into a cohomological
reduction to this statement and a building-theoretic proof of it.
