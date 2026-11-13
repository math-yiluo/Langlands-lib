# `m(u)` fixes the Galois-fixed points of its wall (KP Proposition 9.4.9, restricted form)

Author: Worker 91.

Lean module: `Langlands.Geometry.Building.UnramifiedFixedWallInvarianceStatement`.

This module states one proposition without proof. It isolates the geometric input that
Kaletha–Prasad use to obtain axiom V 5 at the Galois-fixed points of an unramified apartment
(the published `UnramifiedFixedOppositeStatement`). The module
`UnramifiedFixedOppositeReduction` proves that this proposition implies
`UnramifiedFixedOppositeStatement`.

## Data

The binders, instances and the two `let`s are exactly those of
`UnramifiedFixedOppositeStatement` (module `UnramifiedFixedLocusStatement`):

- `F` is a nonarchimedean local field and `K = inertiaFixedField F` is its maximal unramified
  extension;
- `G` is a connected reductive group over `Spec F` (`hG`), with the affine and smooth
  instances from `hG`; `iS : S.toGrp ⟶ G` is a maximal split torus (`hiS`);
- `iT : T.toGrp ⟶ G` and `f : S ⟶ T` satisfy `CommGroupScheme.groupHom f ≫ iT = iS`, and
  `hiT` says that the scalar extension `iT_K` is a maximal split torus of `G_K`;
- `hE` gives opposite factor pairs for `iT_K`;
- `D : KPApartmentData iT_K ω` is an equipollence class of valuations of the root datum of
  `(G_K, T_K)`, where `ω` is the order of `MaximalUnramified.valuation F`. `C` is a centralizer
  datum with full V 6 (`IntegerValuation.IsOmegaCompatible`).

`fixed z` says that `z : D.Apartment` is fixed by `RootFunctionFamily.galoisAction F K T G σ`
for every `σ : K ≃ₐ[F] K`. `φ z` is the published torus-then-field restriction
`torusFieldRestrictedRootFunctionFamily … (D.isRootDatumValuation_of_mem z.mem) f_K`. It is a
root-function family for `(G, S)`. Both are introduced by `let`, with the same bodies as in
`UnramifiedFixedOppositeStatement`.

## Statement

`UnramifiedFixedWallInvarianceStatement.{u}` says the following. Let `z` satisfy `fixed z`.
Let `a ∈ relativeRoots iS`, `g ∈ rootGroupPoints iS a` with `g ≠ 1`, and
`g', g'' ∈ rootGroupPoints iS (-a)`. Let `hm` be a proof of
`g' * g * g'' ∈ normalizerPoints iS`. If `φ z a g = 0`, then

```
(⟨g' * g * g'', hm⟩ : normalizerPoints iS) • φ z = φ z.
```

The action `•` is the published action of `N(F) = normalizerPoints iS` on root-function
families (`RootFunctionFamily.smul_apply`):
`(n • ψ) b v = ψ (n⁻¹ · b) (n⁻¹ v n)`, where `n · b` is `weylAction iS n b`.

In words: write `m = g' g g''` (this is the element `m(u)` of KP Proposition 2.11.17 for
`u = g`). Take a Galois-fixed point `z` on the wall where the restricted value of `g`
vanishes. Then the restricted family at `z` is invariant under `m`.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach` (SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`).

- Proposition 9.4.9, printed pp. 349–350 / PDF pp. 380–381. Its last assertion reads:
  "Moreover, for every `u ∈ U_a(k)*`, `m(u)` acts on `A` by reflection in the hyperplane
  `H_{ψ^u_a}` and the derivative of this action is the reflection `r_a` in `a`." Its proof
  takes `z ∈ H_{ψ^u_a}`, uses assertion (2) (`m(u) ∈ G^0_z(o)`) to see that `m(u)` fixes
  `z`, and concludes that `m(u)` fixes `H_{ψ^u_a}` pointwise.
- Lemma 9.4.15, printed p. 352 / PDF p. 383: the `N(k)`-equivariance of the functions
  `ψ`.
- Proposition 2.11.17 and Remark 2.11.18, printed p. 136 / PDF p. 167: the elements
  `u', u''` and `m(u) = u' u u''`.

### How the Lean statement corresponds to the source

In KP, `A = A(S)` is the apartment of `S` in `B(G_K)^Γ`, and `ψ^u_a` is defined by the fixed
points of `u` in `A`. The Library has neither `B(G_K)` nor the action of `m(u)` on it:
`m(u)` normalizes `S` but in general not `T_K`. The Lean statement therefore uses the
corresponding objects on the side of the root-function families:

- the points of `A(S)` correspond to the Galois-fixed points `z` of `D.Apartment` (KP §9.3);
- `ψ^u_a(z)` corresponds to the restricted value `φ z a g`, so `H_{ψ^u_a}` corresponds to
  the fixed points with `φ z a g = 0`;
- "`m(u)` fixes `z`" is replaced by its consequence on the restricted family:
  `m • φ z = φ z`. This consequence follows from the source assertion together with the
  `N(k)`-equivariance `φ (n · z) = n • φ z` (Lemma 9.4.15; proof of Theorem 9.6.5).

The Lean proposition is therefore a derived formulation of the last assertion of KP
Proposition 9.4.9. It is not a literal transcription: it states only the invariance of the
restricted family, not an action of `m(u)` on points of the apartment of `T_K`.

## Status and use

The proposition is not proved in the Library. `UnramifiedFixedOppositeReduction` proves
`UnramifiedFixedWallInvarianceStatement.{u} → UnramifiedFixedOppositeStatement.{u}`
(KP Corollary 9.4.10). KP prove Proposition 9.4.9 with the Bruhat–Tits group schemes
`G^0_z` and their special fibres (Theorem 8.2.9, printed p. 293 / PDF p. 324).
