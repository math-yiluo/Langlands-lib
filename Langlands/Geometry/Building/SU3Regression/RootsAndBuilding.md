# The quasi-split `SU_3`: relative roots, affine roots, reduced building and depth zero

Module `Langlands.Geometry.Building.SU3Regression.RootsAndBuilding`.

This module states, without proving them, regression examples for Kaletha–Prasad building
data of the quasi-split special unitary group `SU_3` of a separable quadratic extension `E/F`:
the simplest non-split group, and the simplest one with a multipliable relative root. The
statements test the Library's general objects (relative roots, affine roots, facets of the
reduced building, its vertex graph, neutral facet models and their reductive quotients) on
this group in both ramification cases and in every residue characteristic, including `2`.

| KP | statement (namespace `Langlands.Geometry.Building`) |
| --- | --- |
| §2.7 | `SU3RelativeRootsStatement` |
| Corollary 3.2.6 (affine roots) | `SU3AffineRootsStatement` |
| §3.2(f) (vertex and chamber incidence) | `SU3ReducedBuildingStatement` |
| §3.2(f) (the tree) | `SU3ReducedBuildingTreeStatement` |
| Corollary 3.2.6 (the groups `G_v`), Axiom 4.1.22, Proposition 9.4.23, Theorem 9.9.3 | `SU3DepthZeroQuotientsStatement` |

`SU3BuildingRegressionStatement` is the conjunction of the relative-root, affine-root,
incidence and depth-zero statements. The module also contains four auxiliary `Prop`-valued
definitions, described below.
All statements are closed propositions, universe-polymorphic in the universe `u` of `F`.

## The group and the data

Every statement quantifies over

- a nonarchimedean local field `F` of either characteristic (`Field`, `ValuativeRel`,
  `TopologicalSpace`, `IsNonarchimedeanLocalField`), with residue field `𝓀[F]` and
  `q = Nat.card 𝓀[F]`;
- a field `E : Type u` with `Algebra F E`, `Algebra.IsQuadraticExtension F E` and
  `Algebra.IsSeparable F E`;
- a diagonal Hermitian form `H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution F E) Unit`
  and a unit weight `w : Unit → Eˣ` with `hw : ∀ i, (w i : E) = H.weight i`;
- a KP building datum `D : KPBuildingDatum G` for
  `G = HermitianRoot.SchemeModel.groupScheme F E H w hw`, with the premise
  `D.SatisfiesGroupAxioms` (the clauses of KP Definition 4.1.26 that concern `G` alone).

With middle index `Unit`, `G` is the special unitary group of the Hermitian form
`hyperbolic plane ⊕ ⟨w⟩` on `E³`. The Library proves that it is connected reductive
(`HermitianRoot.SchemeModel.isConnectedReductive`) and simply connected
(`HermitianRoot.SchemeModel.isSimplyConnected`). Every quasi-split `SU_3` of `E/F` (KP §2.7,
defined there with the anti-diagonal matrix `J`) is isomorphic to this group for a suitable
weight. The statements are for the Library's model and every weight `w`; they introduce no
other model of `SU_3`, of its building or of its root system.

`P = D.base` is the datum's `ParahoricBuildingData`: its maximal split torus `D.base.i : S → G`,
the apartment `D.base.Apartment` with its affine roots `D.base.affineRoots`
(KP Definition 6.3.4: affine functions `ψ` whose derivative is a relative root `a` with
`U_ψ ⊄ U_{ψ+} · U_{2a}(F)`), the reduced building `D.base.ReducedBuilding` with its
`G(F)`-action, `IsVertex`, `IsChamber`, and the building facets
`BuildingFacet D.base.toValuationBuildingData` (the `IsFacet` subsets).

The premise `D.SatisfiesGroupAxioms` is the standing hypothesis of the setting. The first two
statements do not need it: the relative roots depend only on the maximal split torus, and the
affine roots only on the apartment class, which by KP Proposition 6.2.6
(`omegaCompatibleApartmentUniqueness`) is the unique `ω`-compatible one. The incidence and
tree statements use the building's facets. The depth-zero statement uses the model and
quotient axioms as well.

## Auxiliary definitions

- `IsUnramifiedLocalQuadratic F E`: `v_F(N_{E/F}(z))` is even for every `z ∈ E^×`, where
  `v_F` is the normalized valuation `Plancherel.fieldOrderUnits F` (with `v_F(F^×) = ℤ`) and
  `N_{E/F}` is `Algebra.norm F`.
- `IsRamifiedLocalQuadratic F E`: `v_F(N_{E/F}(z))` is odd for some `z ∈ E^×`.

  Origin: the valuation of `E` extending `v_F` is `w(z) = v_F(N_{E/F}(z))/2` (unique extension
  of a complete discrete valuation to a finite extension), and `w(E^×) ⊇ v_F(F^×) = ℤ` with
  index the ramification index `e ∈ {1, 2}`. So `E/F` is unramified (`e = 1`) exactly when
  every norm has even valuation, and ramified (`e = 2`, a uniformizer of `E` has norm a
  uniformizer of `F`) otherwise. The two predicates are complementary; the formulation needs no
  valuation on `E` and holds in every residue characteristic, including wild ramification.

- `ValuationBuildingData.IsUnramifiedSU3BasePoint B x₀`: for every affine function
  `ψ : B.Apartment →ᵃ[ℝ] ℝ`, `ψ ∈ B.affineRoots` if and only if `ψ.linear = rootForm B.i b`
  for a relative root `b` and `ψ(x₀) ∈ ℤ`. With `x₀` as origin and `A = ℝ`, this is
  KP Corollary 3.2.6 (1): `Ψ = {a + ℤ, -a + ℤ, 2a + ℤ, -2a + ℤ}`.
- `ValuationBuildingData.IsRamifiedSU3BasePoint B a x₀`: `ψ ∈ B.affineRoots` if and only if
  `ψ.linear = rootForm B.i b` for a relative root `b` with either `b ∈ {a, -a}` and
  `ψ(x₀) ∈ ½ℤ`, or `b ∈ {2a, -2a}` and `ψ(x₀) ∈ ½ + ℤ`. This is KP Corollary 3.2.6 (2):
  `Ψ = {a + ½ℤ, -a + ½ℤ, 2a + ½ + ℤ, -2a + ½ + ℤ}`.

The derivative of an affine function on the apartment is a linear form on
`TranslationSpace B.i`, and a relative root `b` gives the form `rootForm B.i b`; the value of
`ψ = b + r` (KP's notation) at the origin `x₀` is `r`.

## The statements

### `SU3RelativeRootsStatement` (KP §2.7)

`Module.finrank ℤ (characterLattice D.base.S) = 1`; there is a character `a` of `S` with
`relativeRoots D.base.i = {a, -a, 2 • a, -(2 • a)}` and `2 • a ∈ relativeRoots D.base.i`
(`a` is multipliable); and for every maximal torus `j : T → G` (`IsMaximalTorus j`), `T` is
not a split torus, i.e. `G` is not split. KP §2.7 (printed pp. 108–109) computes
`X_*(S) = ℤ` and `Φ(S, G) = {±a, ±2a}` for the diagonal torus of the quasi-split form;
the absolute rank of `G` is `2`, larger than its `F`-rank `1`.

### `SU3AffineRootsStatement` (KP Corollary 3.2.6)

- If `E/F` is unramified, some `x₀ : D.base.Apartment` satisfies `IsUnramifiedSU3BasePoint`.
- If `E/F` is ramified, there are `a` with `relativeRoots D.base.i = {a, -a, 2a, -2a}` and
  `x₀` with `IsRamifiedSU3BasePoint D.base a x₀`.

**Conventions.** The Library's apartment uses the valuation `ω = localFieldOrder F`, with
`ω(F^×) = ℤ`, KP's normalization in §2.8 and §3.2; the filtration
`U_{a,x,r} = {u ∈ U_a(F) | x_a(u) ≥ r}` and the affine roots (KP Definition 6.3.4) are KP's.
So there is no rescaling. For `ψ` with derivative `±2a` the condition of Definition 6.3.4 is
that `ψ(x₀)` is a jump of the filtration of `U_{2a}(F)`; for `ψ` with derivative `±a` it is
that `ψ(x₀)` is a jump of the induced filtration of `U_a(F)/U_{2a}(F)` (KP §3.2(c),
conditions (1)–(2), printed pp. 152–153). Here a jump is a real `r` with `X_{r+} ≠ X_r`,
where `X_{r+} = ⋃_{s>r} X_s`, as in Definition 1.6.3(1) of the revised §1.6 of the
*Corrections and additions* (PDF pp. 21–23).

These jump sets are those of KP Corollary 3.2.4. KP define them in (3.2.5)–(3.2.6) as the
value sets of the functions `φ_a`, `φ_{2a}`, `φ_{a/2a}` of (3.2.3)–(3.2.4) and identify value
sets with jump sets by Remark 3.2.3. The *Corrections and additions* (PDF p. 26) state that
Remark 3.2.3 is incorrect as stated and supersede it by the revised §1.6. By Fact 1.6.5(2)–(3)
there, a filtration of the form `X_r = {x | φ(x) ≥ r}` is totally discontinuous, and its set of
jumps is the value set of `φ` on `X ∖ {∗}`. The filtrations (3.2.1)–(3.2.2) of `U_{2a}(F)` and
`U_a(F)` are of this form by their definitions with `≥`. The same holds for the unshifted
filtrations of Remark 3.2.10 and for the negative roots (3.2.7). The induced filtration of
`U_a(F)/U_{2a}(F)` is, by Lemma 3.2.2, the filtration `{u ∈ E | ω(u) ≥ r}`, again of this form.
So Fact 1.6.5(3) recovers KP's identification of the jump sets in Corollary 3.2.4, and
Corollary 3.2.6 is unaffected by the correction.

KP normalize the root valuations of §3.2 by the shift `μ = max{ω(x) | x ∈ E, x + x̄ = 1}`
(displays (3.2.1)–(3.2.3) and (3.2.7)), where `μ = 0` unless `E/F` is wildly ramified and
`μ = -s/2` for the ramification break `s` (Lemma 2.8.1). A shift of all root valuations by
`(⟨a, v⟩)_a` is a translation of the point of the apartment, so it changes only the origin.
Because the statement asserts the existence of `x₀`, it is the transported form of
Corollary 3.2.6 for the Library's apartment, valid in every residue characteristic. KP make the
same point in Remark 3.2.10 (§3.2(e), printed pp. 155–156): without the shift, for ramified
`E/F` with `2 ∤ s` the affine roots are `{±a + ½ℤ + ¼, ±2a + ℤ}`, a translate of
`{±a + ½ℤ, ±2a + ½ + ℤ}`.

### `SU3ReducedBuildingStatement` (KP §3.2(f))

A vertex `y` is incident to a chamber `C : BuildingFacet D.base.toValuationBuildingData`
(`D.base.IsChamber C.val`) when `y ∈ D.base.buildingFacetClosure C`, the closed facet: the union
of the building facets preceding `C` in the Library's incidence relation `FacetPrecedes`.
Numbers of incident objects are `Set.ncard`, so each equation also asserts finiteness.

- Every chamber is incident to exactly `2` vertices.
- If `E/F` is unramified, for every unramified base point `x₀`: each vertex in the
  `G(F)`-orbit of `D.base.apartmentMap x₀` is incident to exactly `q³ + 1` chambers, each other
  vertex to exactly `q + 1` chambers, and of two distinct vertices of one chamber exactly one
  lies in that orbit.
- If `E/F` is ramified, every vertex is incident to exactly `q + 1` chambers.

KP §3.2(f) (printed p. 156): the building is a tree; for ramified `E/F` it is regular of degree
`#P¹(𝔣) = q + 1`; for unramified `E/F` the two ends of each edge have degrees `q + 1` and
`q³ + 1`, the latter at the hyperspecial vertices. With the affine roots of Corollary 3.2.6 (1)
the walls of the apartment are the points `x` with `⟨a, x - x₀⟩ ∈ ½ℤ`; the hyperspecial
vertices of the apartment, where both an `a`-wall and a `2a`-wall pass, are those with
`⟨a, x - x₀⟩ ∈ ℤ`, which form one orbit of the translations by `T(F)` (`ω(a(T(F))) = ℤ`).

### `SU3ReducedBuildingTreeStatement` (KP §3.2(f))

For `B = D.base.toValuationBuildingData`, the simple graph `B.chamberVertexGraph` on
`{y // B.IsVertex y}` is a tree (`SimpleGraph.IsTree`). Two distinct vertices are adjacent
when both belong to `B.buildingFacetVertices C` for a chamber `C`. This is the same incidence
relation used above, since `buildingFacetVertices C` consists of the vertices in
`buildingFacetClosure C`. The graph is defined for general valuation building data in
[`GeneralLinearTreeStatement`](../GeneralLinearTreeStatement.md).

KP §3.2(f) (printed p. 156) describes the building in both ramification cases as a
one-dimensional simplicial tree, with chamber closures as edges. To compare with an
arbitrary `D`, `ValuationBuildingData.exists_isEquivariantBuildingIso_id` identifies
apartments affinely and carries facets to facets. On each rank-one apartment such a
comparison preserves point facets, open interval chambers and their endpoints, hence
it induces an isomorphism of the vertex graphs. The tree statement uses the same
`D.SatisfiesGroupAxioms` premise and holds for either ramification case without any
condition on the base point or residue characteristic.

### `SU3DepthZeroQuotientsStatement` (KP Corollary 3.2.6, Axiom 4.1.22, Proposition 9.4.23, Theorem 9.9.3)

For a building facet `x`, `𝒢_x = (D.models.facetModels.model x).neutral` is its neutral model,
whose integral points are the parahoric `D.parahoric x`, and `Ḡ_x = D.reductiveQuotient x` is
the specified quotient of its special fibre `𝒢_x ⊗ 𝓀[F]`; the axioms make it the maximal
reductive quotient. `#Ḡ_x(𝓀)` is `Nat.card (D.reductiveQuotientPoints x)`, so each equation
also asserts finiteness. The facet of a vertex `y` is any building facet `x` with `y ∈ x.val`
(under the axioms, `x.val = {y}`).

- Unramified `E/F`, unramified base point `x₀`, vertex `y` in the `G(F)`-orbit of
  `D.base.apartmentMap x₀`: `IsConnectedReductive (𝒢_x ⊗ 𝓀[F])` and
  `#Ḡ_x(𝓀) = q³(q² - 1)(q³ + 1)`.
- Unramified `E/F`, any other vertex: `¬ IsConnectedReductive (𝒢_x ⊗ 𝓀[F])` and
  `#Ḡ_x(𝓀) = q(q² - 1)(q + 1)`.
- Unramified `E/F`, chamber `C`: `#Ḡ_C(𝓀) = q² - 1`.
- Ramified `E/F`, every vertex: `¬ IsConnectedReductive (𝒢_x ⊗ 𝓀[F])` and
  `#Ḡ_x(𝓀) = q(q² - 1)`.
- Ramified `E/F`, chamber `C`: `#Ḡ_C(𝓀) = q - 1`.

The subtractions are in `ℕ`, where `q ≥ 2` makes them exact.

#### Origin of the numbers

For a building facet `x`, let `S̄ ⊂ Ḡ_x` be the image of the special fibre of the datum's closed
split integral torus, and `Φ_x` the set of derivatives of the affine roots vanishing on `x`. The
numbers below are first computed for the Bruhat–Tits models of KP; the paragraph *Every datum*
explains why they hold for the models of every datum `D` with `D.SatisfiesGroupAxioms`.

*Relative roots over `𝓀`.* `Ḡ_x` is connected reductive over the finite field `𝓀`, and `S̄`
is a maximal `𝓀`-split torus of it (KP Axiom 4.1.22(3)). Its relative root datum with respect
to `S̄` is `(X^*(S), Φ_x, X_*(S), Φ_x^∨)`. This is Axiom 4.1.22(6), the field
`derivative_root_data` of `BuildingModelQuotientFamily.FacetAxiomClauses` contained in
`D.SatisfiesGroupAxioms`; KP Proposition 9.4.23 proves it for the Bruhat–Tits models. Write
`t = ⟨a, x - x₀⟩` for a point `x` of the apartment. With the affine roots of
`SU3AffineRootsStatement`:

- unramified `E/F`: the affine roots `±a + ℤ` vanish where `t ∈ ℤ` and `±2a + ℤ` where
  `t ∈ ½ℤ`. So `Φ_x = {±a, ±2a}` at the vertices `t ∈ ℤ` (the orbit of `x₀`) and
  `Φ_x = {±2a}` at the vertices `t ∈ ½ + ℤ`;
- ramified `E/F`: `±a + ½ℤ` vanish where `t ∈ ½ℤ` and `±2a + ½ + ℤ` where `t ∈ ¼ + ½ℤ`. So
  `Φ_x = {±a}` at the vertices `t ∈ ½ℤ` and `Φ_x = {±2a}` at the vertices `t ∈ ¼ + ½ℤ`;
- at a chamber `Φ_C = ∅`, and `Ḡ_C` is a torus. The Library proves this as
  `facetQuotient_isTorus_iff_isChamber`.

With `x₀` as origin, these are the groups `G_0`, `G_{1/2}` (unramified) and `G_0`, `G_{1/4}`
(ramified) of KP Corollary 3.2.6.

*The torus.* Over the finite field `𝓀`, `Ḡ_x` is quasi-split (Lang's theorem), and
`Z̄ = Z_{Ḡ_x}(S̄)` is a maximal torus. For KP's models it is the torus `𝒯 = R_{𝔣_E/𝔣} 𝔾_m` of
KP §3.2(a) and (c), with
`𝒯(𝔣) = T(F)_0/T(F)_{0+} = 𝔣_E^×`, where `T = Z_G(S) ≅ R_{E/F} 𝔾_m`. It has dimension `2` and
`q² - 1` points if `E/F` is unramified. If `E/F` is ramified, then `𝔣_E = 𝔣`, and it is `𝔾_m`,
of dimension `1` with `q - 1` points. At a chamber, `Ḡ_C = Z̄`.

*Root groups and the Bruhat count.* At a vertex, `Ḡ_x` has `𝓀`-rank one. Let `B̄ = Z̄ ⋉ Ū` be
the Borel subgroup whose unipotent radical `Ū` is the root group of the positive elements of
`Φ_x` (for `Φ_x = {±a, ±2a}` it contains the `2a` root group). The Bruhat decomposition
`Ḡ_x(𝓀) = B̄(𝓀) ⊔ Ū(𝓀) n B̄(𝓀)`, for `n` representing the nontrivial Weyl element, gives

```text
#Ḡ_x(𝓀) = #Z̄(𝓀) · #Ū(𝓀) · (#Ū(𝓀) + 1).
```

Here `#Ū(𝓀) + 1 = [Ḡ_x(𝓀) : B̄(𝓀)]` is the number of Borel subgroups of `Ḡ_x`. By
Axiom 4.1.22(5) (the field `parabolic_order`) it is the number of chambers incident to `x`. For
KP's models, `Ū(𝓀)` is the quotient `U_a(F)_{⟨-a, v⟩}/U_a(F)_{⟨-a, v⟩+}`, for the coordinate
`v` of the vertex in KP's apartment, described by Lemma 3.2.5 and the discussion before
Corollary 3.2.6 (printed pp. 150–152). At a vertex of the orbit of `x₀`
in the unramified case, it is `U_{𝔣_E/𝔣}(𝔣) = {(u, v) ∈ 𝔣_E² | u ū = v + v̄}`, with `q³`
elements (Lemma 3.2.5(4)). At every other vertex it is a one-dimensional `𝔣`-vector space, with
`q` elements (Lemma 3.2.5(2)–(3)). Hence:

- unramified, vertex of the orbit of `x₀`: `Ḡ_x` is the quasi-split `SU_3` of `𝔣_E/𝔣`, and
  `#Ḡ_x(𝓀) = (q² - 1) q³ (q³ + 1)`;
- unramified, other vertex: `Φ_x = {±2a}`, the derived group is `SL_2`, and
  `#Ḡ_x(𝓀) = (q² - 1) q (q + 1)`;
- ramified, every vertex: `Ḡ_x` is `PGL_2` (`Φ_x = {±a}`) or `SL_2` (`Φ_x = {±2a}`), and in
  both cases `#Ḡ_x(𝓀) = (q - 1) q (q + 1) = q(q² - 1)`.

The numbers of chambers `#Ū(𝓀) + 1`, that is `q³ + 1` and `q + 1`, are those of
`SU3ReducedBuildingStatement`.

*Reductivity.* The neutral special fibre is smooth and connected of dimension `dim G = 8`, by
smoothness of the model, as in the proof of KP Proposition 8.4.14. It is reductive exactly when
its unipotent radical, which is smooth and connected, is trivial, that is when
`dim Ḡ_x = 8`. The big cell `Ū^- × Z̄ × Ū` gives `dim Ḡ_x = dim Z̄ + 2 · dim Ū`. For KP's models
`dim Ū` is `3` at the vertices of the orbit of `x₀` in the unramified case and `1` elsewhere,
so `dim Ḡ_x` is `2 + 6 = 8` at those vertices, `2 + 2 = 4` at the other unramified vertices
and `1 + 2 = 3` in the ramified case. So the neutral special fibre is reductive exactly at the
vertices of the orbit of `x₀` in the unramified case. This agrees with KP Theorem 9.9.3(1): the
parahoric model of `x` is reductive if and only if `x` is hyperspecial, that is, a vertex that
is special in `B(G_K)` with `G_K` split, for `K` the maximal unramified extension (as recalled
before Theorem 9.9.3). For unramified `E/F`, `G_K` is split, and the hyperspecial vertices are
those of the orbit of `x₀` (§3.2(f)). For ramified `E/F`, `E ⊗_F K` is a field, so `G_K` is
not split and there is no hyperspecial vertex.

KP's Theorem 8.4.10 and Remark 8.4.11 describe the quotient over the residue field of `K`.
There the root system at a vertex of the orbit of `x₀` is the absolute system `A₂` with six
roots, and at an extra special vertex of the ramified group the quotient is `SO(3) = PGL_2`.
Proposition 8.4.14 assumes that `G` splits over `K`, so it applies only to the unramified case.
The relative statements over `𝓀` used here are Axiom 4.1.22(6) and Proposition 9.4.23.

*Every datum.* The statements concern an arbitrary datum `D` with `D.SatisfiesGroupAxioms`,
whose models are not assumed to be KP's. The numbers are the same:

- By Axiom 4.1.20, `D.parahoric x` is the parahoric subgroup `P_x`: the pointwise fixer of
  `x` in `G(F)^0`. The building with its `G(F)`-action is unique up to `G(F)`-equivariant
  isomorphism (`ValuationBuildingData.exists_isEquivariantBuildingIso_id`).
- The reduction `P_x → Ḡ_x(𝓀)` (`D.parahoricReduction x`) is surjective, by Hensel's lemma
  for the smooth neutral model and Lang's theorem for its smooth connected unipotent radical.
  Its kernel `P_{x,0+}` (`D.parahoricRadical x`, Axiom 4.1.22(7)) is pro-`p`: it is an
  extension of the `p`-group `R_u(𝓀)` by the first congruence subgroup. The group
  `Ḡ_x(𝓀)` has no nontrivial normal `p`-subgroup. At a chamber it is the group of points of a
  torus, of order prime to `p`. At a vertex, `#Z̄(𝓀)` is prime to `p` and
  `#Ū(𝓀) + 1 ≡ 1 (mod p)`, so the Bruhat count shows that `Ū(𝓀)` and the opposite
  `Ū^-(𝓀)` are Sylow `p`-subgroups; a normal `p`-subgroup lies in both, and they meet
  trivially. Hence `P_{x,0+}` is the largest normal pro-`p` subgroup of `P_x`, and
  `#Ḡ_x(𝓀) = [P_x : P_{x,0+}]` depends only on the subgroup `P_x` of `G(F)`. It is the order
  computed above for KP's models.
- The dimension count uses only the supplied axioms and these orders. The number of chambers
  at a vertex `x` is `#Ū(𝓀) + 1`, and `#Ū(𝓀) = q^{dim Ū}` because `Ū` is split unipotent over
  the perfect field `𝓀`. So `dim Ū` is `3` at the vertices of the orbit of `x₀` in the
  unramified case and `1` elsewhere. `Z̄` is the image in `Ḡ_x` of the special fibre of the
  centralizer of the integral split torus in the neutral model, as in the proof of KP
  Proposition 9.4.25. That centralizer is the centralizer of a cocharacter generating the
  torus, a smooth closed subgroup scheme with generic fibre `Z_G(S) = T` (KP
  Proposition 2.11.3(1), as applied in the proof of Lemma 9.4.20 to any smooth affine model
  with a closed split torus). Its special fibre has dimension `dim T = 2`, so `dim Z̄ ≤ 2`.
  At the vertices outside the orbit of `x₀`, and at all vertices in the ramified case,
  `dim Ḡ_x ≤ 2 + 2 = 4 < 8`, and the neutral special fibre is not reductive. At a vertex of
  the orbit of `x₀`, `#Z̄(𝓀) = #Ḡ_x(𝓀)/(q³(q³ + 1)) = q² - 1 ≠ q - 1`. So
  `Z̄ ≠ S̄`, `dim Z̄ = 2` and `dim Ḡ_x = 8`. The unipotent radical is then trivial, and the
  neutral special fibre equals `Ḡ_x` and is connected reductive.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (PDF page = printed page
  + 31):
  - Proposition 2.11.3(1), smoothness of the centralizer of a cocharacter (printed p. 131,
    PDF 162);
  - §2.7, the group `SU_3` and its relative roots and root groups (printed pp. 108–110,
    PDF 139–141); §2.8 and Lemma 2.8.1, the number `μ` and the jumps of the trace-zero
    filtration, including wild ramification (printed pp. 110–112, PDF 141–143);
  - §3.2, the example of `SU_3` (printed pp. 147–156, PDF 178–187): the torus filtration of
    §3.2(a) (printed p. 148, PDF 179); the filtrations (3.2.1)–(3.2.3), Lemma 3.2.2 and the
    jump sets (3.2.5)–(3.2.6) (printed pp. 148–150, PDF 179–181); Corollary 3.2.4 and
    Lemma 3.2.5 (printed pp. 150–151, PDF 181–182); the negative roots (3.2.7) (printed p. 151,
    PDF 182); the standard apartment, the groups `G_v` and the affine roots with
    Corollary 3.2.6 and Remark 3.2.7 (printed pp. 152–153, PDF 183–184); the unshifted
    filtrations of Remark 3.2.10 (§3.2(e), printed pp. 155–156, PDF 186–187); the shape of the
    tree (§3.2(f), printed p. 156, PDF 187);
  - Axioms 4.1.20 and 4.1.22 (printed pp. 163–164, PDF 194–195);
  - Theorem 8.4.10 and Remark 8.4.11, the quotient over the residue field of `K` (printed
    pp. 305–306, PDF 336–337); Proposition 8.4.14 and its dimension argument, for `G` split over
    `K` (printed p. 306, PDF 337);
  - Lemma 9.4.20 (printed pp. 354–355, PDF 385–386); Proposition 9.4.23, the relative root datum
    of the reductive quotient over the residue field of `F`, and Proposition 9.4.25 with its
    proof (printed pp. 357–358, PDF 388–389);
  - Theorem 9.9.3(1) and the recollection of hyperspecial vertices before it (printed p. 380,
    PDF 411).
- Kaletha–Prasad, *Corrections and additions* (1 November 2024),
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  - the revised §1.6, in particular Definition 1.6.3 and Fact 1.6.5(2)–(3) (PDF pp. 21–23);
  - the Chapter 3 entry stating that Remark 3.2.3 is incorrect as stated and is superseded by
    the revised §1.6 (PDF p. 26); there is no entry on §2.7 and no other entry on §3.2;
  - the corrected Definition 4.1.26 (PDF p. 27), whose one-group clauses are
    `KPBuildingDatum.SatisfiesGroupAxioms`.
