# Opposite factors at depth zero on the Galois-fixed points (KP Proposition 9.4.9(2), restricted form)

Author: Worker 169.

Lean module: `Langlands.Geometry.Building.UnramifiedFixedDepthZeroOppositeStatement`.

This module states one proposition without proof:
`UnramifiedFixedDepthZeroOppositeStatement`. It is the part of Kaletha–Prasad
Proposition 9.4.9 that needs the special fibre of the parahoric group scheme `G^0_z`
(Theorem 8.2.9). KP use Proposition 9.4.9 to prove V 5 (Corollary 9.4.10), and the
published `UnramifiedFixedOppositeStatement` states V 5 at the Galois-fixed points of an
unramified apartment. The module contains one private instance, which supplies
`IsAffineHom` for the base change of `G` to `K`, and no theorem.

## Common data

The binders, instances and the two `let`s are exactly those of
`UnramifiedFixedOppositeStatement` (module `UnramifiedFixedLocusStatement`):

- `F` is a nonarchimedean local field and `K = inertiaFixedField F` is its maximal
  unramified extension;
- `G` is a connected reductive group over `Spec F` (`hG`), with the affine and smooth
  instances from `hG`; `iS : S.toGrp ⟶ G` is a maximal split torus (`hiS`);
- `iT : T.toGrp ⟶ G` and `f : S ⟶ T` satisfy `CommGroupScheme.groupHom f ≫ iT = iS`, and
  `hiT` says that the scalar extension `iT_K` is a maximal split torus of `G_K`;
- `hE` gives opposite factor pairs for `iT_K`;
- `D : KPApartmentData iT_K ω` is an equipollence class of valuations of the root datum of
  `(G_K, T_K)`, where `ω` is the order of `MaximalUnramified.valuation F`. `C` is a
  centralizer datum with full V 6 (`IntegerValuation.IsOmegaCompatible`).

`fixed z` says that `z : D.Apartment` is fixed by
`RootFunctionFamily.galoisAction F K T G σ` for every `σ : K ≃ₐ[F] K`. `φ z` is the
published torus-then-field restriction
`torusFieldRestrictedRootFunctionFamily … (D.isRootDatumValuation_of_mem z.mem) f_K`. It is
a root-function family for `(G, S)` with values in `WithTop ℝ`. Both are introduced by
`let`, with the same bodies as in `UnramifiedFixedOppositeStatement`.

## Statement

`UnramifiedFixedDepthZeroOppositeStatement.{u}` says the following. Let `z` satisfy
`fixed z`. Let `a ∈ relativeRoots iS` and `g ∈ rootGroupPoints iS a` with `g ≠ 1` and
`φ z a g = 0`. Let `g', g'' ∈ rootGroupPoints iS (-a)` with
`g' * g * g'' ∈ normalizerPoints iS`. Then

```
0 ≤ φ z (-a) g' ∧ 0 ≤ φ z (-a) g''.
```

In words: write `m = g' g g''`. This is the element `m(u)` of KP Proposition 2.11.17 for
`u = g`. If `z` is a Galois-fixed point on the wall where the restricted value of `g`
vanishes, then both opposite factors have restricted value at least `0` at `z`.

The statement does not assume `g' ≠ 1` or `g'' ≠ 1`. If one of them is `1`, its value is
`⊤` and that inequality holds trivially. By KP Proposition 2.11.17 both factors are in fact
nontrivial.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach` (SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`).

- Proposition 9.4.9, printed p. 349 / PDF p. 380. Let `a ∈ Φ`, `u ∈ U_a(k)^*`, and let
  `z` be a point of `H_{ψ^u_a}`, that is `ψ^u_a(z) = 0`. Let `G^0_z` be the parahoric
  `o`-group scheme of `z`. Two equivalent assertions hold: (1) the image of `u` in
  `G^0_z(f)` does not lie in `R_u(G^0_z)(f)`; (2) for `m(u) = u' u u''`, the elements
  `u'`, `u''` and `m(u)` lie in `G^0_z(o)`. The proof, printed pp. 349–350 / PDF
  pp. 380–381, derives (1) from Axiom 4.1.22(4) and Proposition 9.4.3(3), and gets the
  equivalence of (1) and (2) from Theorem 8.2.9 (printed p. 293 / PDF p. 324).
- Proposition 9.4.3(3), printed p. 346 / PDF p. 377: for `v ∈ U_b(k)^*`, the set of points
  of `A` fixed by `v` is the half-apartment `A_{ψ^v_b} = {x | ψ^v_b(x) ≥ 0}`.
- Proposition 2.11.17, printed p. 136 / PDF p. 167: the unique `u', u'' ∈ U_{-a}(k)` such
  that `m(u) = u' u u''` normalizes `S`. They lie in `U_{-a}(k)^*`.
- Construction 9.6.1, printed p. 365 / PDF p. 396: `ϕ^x_b(v) = ψ^v_b(x)`.
- Corollary 9.4.10, printed p. 350 / PDF p. 381: `ψ^{u'}_{-a} = -ψ^u_a = ψ^{u''}_{-a}`.

The *Corrections and additions* (1 November 2024), `kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 39–41, correct Proposition 9.4.8 but not Proposition 9.4.9.

### How the Lean statement corresponds to the source

In KP, `A = A(S)` is the apartment of `S` in `B(G_K)^Γ`. The Lean statement uses the
correspondences already used for `UnramifiedFixedOppositeStatement`:

- the points of `A(S)` correspond to the Galois-fixed points `z` of `D.Apartment` (KP §9.3);
- `ψ^v_b(z)` for `v ∈ U_b(k)^*` corresponds to the restricted value `φ z b v`
  (Construction 9.6.1; the published restriction equals `ϕ^z` by Lemma 9.6.3, as recorded
  in the Markdown of `UnramifiedValuationDescentStatement`). The hypothesis `φ z a g = 0`
  is therefore `z ∈ H_{ψ^u_a}` for `u = g`;
- `g'` and `g''` are the `u'` and `u''` of Proposition 2.11.17, by its uniqueness
  assertion.

The conclusion is a consequence of assertion (2), not assertion (2) itself. The group
`G^0_z(o)` fixes `z`, so `u'` and `u''` fix `z`. By Proposition 9.4.3(3) this means
`ψ^{u'}_{-a}(z) ≥ 0` and `ψ^{u''}_{-a}(z) ≥ 0`, that is `0 ≤ φ z (-a) g'` and
`0 ≤ φ z (-a) g''`. The Lean statement says nothing about `m(u)`, about `G^0_z` or about
its special fibre.

The inequalities are also a consequence of Corollary 9.4.10, which gives equality with
`-ψ^u_a(z) = 0`. KP prove Corollary 9.4.10 from Proposition 9.4.9, so the statement
records the part of Proposition 9.4.9 that is proved first and that needs Theorem 8.2.9.

## Intended use

The proposition is one of two inputs for `UnramifiedFixedWallInvarianceStatement`
(staged by Worker 91 under Task 6012). The other input is the published
`UnramifiedFixedLeviTransportStatement`. A separate reduction module will prove that the
two statements together imply `UnramifiedFixedWallInvarianceStatement`, from which
`UnramifiedFixedOppositeReduction` gives `UnramifiedFixedOppositeStatement`.

## Provenance and scope

The provenance is derived. KP work over Henselian discretely valued fields with perfect
residue field; here `F` is a nonarchimedean local field. KP state Proposition 9.4.9 for
the descended building `B(G_K)^Γ` and the affine functions `ψ^u_a`. The Lean statement uses
the Library's `D.Apartment`, its Galois action and the published restriction `φ`, and
keeps only the inequalities for the opposite factors.

The proposition is not proved here. A proof needs the parahoric group scheme `G^0_z`, its
special fibre and the rank-one Bruhat decomposition behind Theorem 8.2.9, which the Library
does not yet have.
