# Chambers stable under a twisted Galois action over the maximal unramified extension

This module states `UnramifiedTwistedChamberStatement`: for a connected reductive group over a
nonarchimedean local field, the building over the maximal unramified extension contains a
chamber stable under the Galois action twisted by any finite-level cocycle. Nothing in this
module is proved.

## Statement

Let `F` be a nonarchimedean local field (at universe `u`), `K = inertiaFixedField F` its
maximal unramified extension inside the separable closure, `Γ = Aut(K/F)` (`K ≃ₐ[F] K`) and
`G_K = baseChanged F K G`. The proposition quantifies over

- an `F`-group scheme `G` with `IsConnectedReductive G`;
- a commutative `F`-group scheme `T` with a homomorphism `iT : T → G` whose scalar extension
  `T_K → G_K` is a maximal `K`-split torus (`hiT`), that is, an `F`-torus of `G` that becomes a
  maximal split torus over `K`;
- an equipollence class `D` of valuations of the root datum of `(G_K, T_K)` for the order of
  the normalized valuation of `K`, a centralizer datum `C` of `T_K`, axiom V 6 for `D` and
  `C` (`h6`), and the stability of `D` under the coefficient action of `Γ` (`hD`).

These data give the building data `UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6`
of `G_K` on the apartment of `T_K` (with `hGK` the connected reductivity of `G_K` from
`connectedReductiveFieldExtensionStatement`), and its semilinear Galois data
`UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD`. The action
`σ ↦ (semilinearData …).action σ` on the reduced building is the coefficient action of `Γ`,
`KPApartmentData.galoisQuotientAction` (`UnramifiedBuildingDescent.semilinearData_action_apply`),
and satisfies `action σ (g • y) = σ(g) • action σ y` with `σ(g) = rationalConjugate F K G σ g`.

The proposition asserts: for every map `c : Γ → G(K)` that is a crossed homomorphism,
`c (σ * τ) = c σ * σ(c τ)` for all `σ, τ`, and is trivial on the fixing subgroup of some
finite-dimensional intermediate field `E` of `K/F`, there is a subset `Y` of the reduced
building with

1. `Y` a chamber of the building data (`IsChamber`: a `G(K)`-translate of the image of a
   chamber of the apartment for its affine roots);
2. `(fun y => c σ • action σ y) '' Y = Y` for every `σ ∈ Γ`: `Y` is stable under the twisted
   action `y ↦ c(σ) · σ(y)`.

For `c = 1` this is a `Γ`-stable chamber.

## Source

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), with `k = F` and `K` its maximal
unramified extension:

- Proposition 9.10.4 (printed p. 382, PDF p. 413): if `dim(f) ≤ 1`, which holds for the finite
  residue field `f` of `F`, every connected reductive `k`-group is residually quasi-split; by
  Proposition 9.10.1, (4) ⇒ (1) (printed p. 381, PDF p. 412), `B(G_K)` then contains a
  `Γ`-invariant `K`-chamber.
- Proof of Theorem 10.6.1 (printed p. 397, PDF p. 428): for a cocycle `c` of `Γ` in `G(K)`,
  the twist `_cG` has the same building `B` over `K`, with the twisted action
  `x ↦ c(γ) γ(x)`; Proposition 9.10.4 applied to `_cG` gives a chamber `C′` of `B` stable under
  the twisted action.
- §9.2.1 (printed pp. 325–326, PDF pp. 356–357) for the action of `Γ` on `B(G_K)` through
  a `Γ`-stable apartment of a special torus.

The finiteness hypothesis on `c` expresses that `c` is continuous for the profinite topology
of `Γ` (it is constant on the cosets of the open subgroup fixing `E`), so that `_cG` is a
`k`-form of `G` and the source applies to it.

## Provenance

This is a derived statement, not a numbered result of the source. It combines Propositions
9.10.1 and 9.10.4 with the twisting step of the proof of Theorem 10.6.1, and is formulated
with the Library's supplied apartment class `D` of a special torus and its coefficient
action instead of the constructed building of `_cG`. It does not assert that the data `D`, `C`
exist; existence for a special torus comes from `QuasiSplitIntegerApartmentExistenceStatement`
and the Galois stability from `MaximalUnramified.galoisStable_of_isOmegaCompatible`.
