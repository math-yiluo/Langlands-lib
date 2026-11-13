# Apartment-compatible descent of the building from the maximal unramified extension

`Langlands.Geometry.Building.UnramifiedApartmentDescentStatement` is an
unproved proposition. The module also proves one lemma: the proposition
implies the published `UnramifiedBuildingDescentStatement`.

## The statement

The proposition is universe polymorphic. At each universe `u` it ranges over
every `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, in equal and mixed characteristic. It also
ranges over every group scheme `G` over `Spec F` with a proof
`hG : IsConnectedReductive G`, and every `B : ValuationBuildingData G`. The
instance `IsAffineHom G.X.hom` is derived from `hG`; it is not a premise. No
building axiom is assumed of `B`. The binders are exactly those of the
published `UnramifiedBuildingDescentStatement`.

Write `L = inertiaFixedField F` for the maximal unramified extension and
`G_L = baseChanged F L G`. The conclusion asserts that there exist
`C : MaximalUnramified.BuildingData F G_L`,
`D : MaximalUnramified.SemilinearApartmentData C`,
`e : B.ReducedBuilding → C.ReducedBuilding` and a real affine map
`a : B.Apartment →ᵃ[ℝ] C.Apartment`, such that:

1. `e` is injective;
2. `e (g • z) = rationalExtend F L G g • e z` for every
   `g : rationalPoints G`;
3. `e (B.apartmentMap w) = C.apartmentMap (a w)` for every point `w` of the
   apartment of `B`;
4. `D.action σ (e z) = e z` for every `σ : L ≃ₐ[F] L` and every `z`;
5. every point `y` of `C.ReducedBuilding` fixed by `D.action σ` for every `σ`
   is `e z` for some `z`;
6. if `e z` is a special point of `C`, then `z` is a special point of `B`;
7. for every point `w` of the apartment of `B`,
   `a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) = AffineRootSystem.facet B.affineRoots w`;
8. for every `s` in
   `characterValuationKernel (MaximalUnramified.valuation F) (baseChanged F L B.S.toGrp)`
   and every point `w` of the apartment of `B`, the image of `s` in `G(L)`
   fixes `e (B.apartmentMap w)`. The image is
   `rationalPoints.map ((GroupScheme.baseChange (baseMap F L)).map B.i) s`,
   where `B.i : B.S.toGrp ⟶ G` is the maximal split torus of the apartment
   presentation of `B`.

Clauses 1, 2, 5 and 6 are the four clauses of the published statement.
Clauses 3, 4, 7 and 8 are new. Clause 3 says that `e` maps the apartment of `B`
into the apartment of `C` by a real affine map. With clause 2 it follows that
`e` maps each translated apartment chart `g · A(S)` of `B` affinely into the
chart `rationalExtend g · A` of `C`. So a nonempty bounded subset of a chart
of `B` goes to a nonempty bounded subset of a chart of `C`. Clause 4 says that
the image of `e` consists of Galois-fixed points. Clauses 4 and 5 together
identify the image of `e` with the full Galois-fixed locus.

Clause 7 is about facets in the sense of the Library's
`AffineRootSystem.facet`: the class of a point for the relation "same sign
under every affine root" (KP Remark 1.3.16, Bourbaki's facets). It says that
the facet of `w` for the affine roots `B.affineRoots` of `B` is exactly the
set of points of the apartment of `B` whose image under `a` lies in the facet
of `a w` for the affine roots `C.affineRoots` of `C`. In particular `a` maps
each facet of the apartment of `B` into one facet of the apartment of `C`.

Clause 8 is about the maximal split torus `S` of the apartment of `B`. The
group `characterValuationKernel (MaximalUnramified.valuation F) S_L` is the
group `S(L)^1` of points of `S_L` on which every character has valuation
zero. Since `S_L` is split, it is the maximal bounded subgroup `S(L)^b` of
`S(L)`. Clause 8 says that this subgroup, mapped into `G(L)` along `B.i`,
fixes every point of the image under `e` of the apartment of `B`.

## Source correspondence

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

* §9.2.1, printed pp. 325–326 / PDF pp. 356–357, defines the action of
  `Γ = Gal(K/k)` on `B(G_K)`. It satisfies `γ(g · x) = γ(g) · γ(x)`, and
  for each apartment `A` the action map `A → γ(A)` is affine.
* §9.2.3, printed p. 326 / PDF p. 357, defines `B = B(G_K)^Γ`. Its
  apartments are `A^Γ` for special `k`-apartments `A`.
* Proposition 9.3.13, printed p. 338 / PDF p. 369. For a special `k`-torus
  `T ⊇ S` with apartment `A`, it gives `B(G_K)^Γ_S = A^Γ`, an affine
  subspace of `A`. §9.3.14, printed p. 338 / PDF p. 369, names this affine
  space `A(S)`. Proposition 9.3.16, printed p. 339 / PDF p. 370, shows that
  `A(S) = B(G_K)^Γ_S` satisfies Axiom 4.1.4, so it is the apartment of `S`.
* Theorem 9.2.7, printed p. 329 / PDF p. 360: `B` is the building of
  `G(k)`.
* Theorem 9.6.5 and §9.6.6, printed pp. 366–367 / PDF pp. 397–398, identify
  `B(G_K)^Γ` `G(k)`-equivariantly with the Chapter 7 valuation quotient.
* Proposition 9.9.2, printed p. 380 / PDF p. 411: a point of `B(G)` that is
  special in `B(G_K)` is special in `B(G)`.
* §9.2.4, printed p. 327 / PDF p. 358, defines the facets of `B` as the
  intersections `𝔉 ∩ B` with the `Γ`-invariant facets `𝔉` of `B(G_K)`.
* Proposition 9.4.28, printed pp. 359–360 / PDF pp. 390–391. For a special
  `k`-apartment `A ⊇ A(S)` with special torus `T ⊇ S`, every relative affine
  root `ψ ∈ Ψ(S, G)` is the restriction to `A(S)` of an absolute affine root
  of `Ψ(T, G)` with the same vanishing point. Conversely, the restriction to
  `A(S)` of an absolute affine root is either constant or a relative affine
  root.
* Corollary 9.4.31, printed p. 361 / PDF p. 392: the facets of `A(S)` defined
  in §9.2.4 coincide with the facets determined by the affine root
  hyperplanes as in Remark 1.3.16.
* The paragraph before Proposition 9.3.11, printed p. 337 / PDF p. 368. For
  a `k`-split torus `S` with maximal bounded subgroup `S(K)^b`, it defines
  `B(G_K)_S` as the set of points of `B(G_K)` fixed by `S(K)^b`, and
  `B(G_K)^Γ_S` as its `Γ`-fixed part. Proposition 9.3.16, printed p. 339 /
  PDF p. 370, starts from the equality `A(S) = B(G_K)^Γ_S`.
* The proof of Proposition 9.3.4, printed p. 332 / PDF p. 363, writes the
  maximal bounded subgroup of `S(K)` as `S(K)^1`.
* Proposition 2.5.8, printed p. 88 / PDF p. 119. For a torus `T` over a
  field with valuation `ω`, the maximal bounded subgroup `T(k)^b = T(k)^1`
  is the set of `x` with `ω(χ(x)) = 0` for every rational character `χ`.

The authors' corrections, registered as `kaletha-prasad-2024-corrections`
(version of 1 November 2024, PDF pp. 39–40), replace the paragraph of §9.2.1
on orbit finiteness. They also add a paragraph on `Γ`-stable fixed points to
§9.2.1. They amend the proof of Proposition 9.3.11 and the statement and
proof of Proposition 9.3.12; this Markdown cites neither of them. Before
Proposition 9.3.13 they add a construction of the `V(S')`-action on
`B(G_K)^Γ_S`, and they delete the last paragraph of its proof. The cited
statements are unchanged.

As in the published statement, `e` is the inclusion of `B(G_K)^Γ` into
`B(G_K)`, composed with the identification of §9.6.6. On the apartment
`A(S) = A^Γ` this inclusion is the inclusion of an affine subspace of `A`.
The upstairs data `C` are taken on a special `k`-apartment `A`. Clause 3 then
holds with `a` the affine inclusion of `A^Γ` into `A`. Clause 4 holds because
the image is contained in `B(G_K)^Γ`. Clauses 1, 2, 5 and 6 have the sources
recorded in the published statement's Markdown.

Clause 7 follows from Proposition 9.4.28 for this `a`. Let `w, w'` be points
of `A(S)`. If `w` and `w'` have the same sign under every absolute affine
root, then they have the same sign under every relative affine root, because
each relative affine root is a restriction of an absolute one. Conversely,
if they have the same sign under every relative affine root, then they have
the same sign under every absolute affine root, because its restriction is
constant or relative. So `a w'` lies in the facet of `a w` exactly when `w'`
lies in the facet of `w`. This is the apartment form of Corollary 9.4.31.
The Library's `C.affineRoots` and `B.affineRoots` are the sets `Ψ` of KP
Definition 6.3.4 for the two apartment classes. These are the source's
`Ψ(T, G)` and `Ψ(S, G)`: see Proposition 6.4.8 and §9.4.27 for the former.
For the latter, §9.6.6 (printed p. 367 / PDF p. 398) identifies the affine
roots of Definition 6.3.4 for the descended valuation of Theorem 9.6.5 with
the affine roots of 9.4.12.

Clause 8 holds by the definition of `A(S)` in these sources. The apartment
`A(S)` of `B` is `B(G_K)^Γ_S`, and every point of `B(G_K)_S` is fixed by
`S(K)^b`. So `S(K)^b` fixes the image of `A(S)` in `B(G_K)` pointwise. For
the split torus `S_K` every character is rational over `K`. By Proposition
2.5.8 the subgroup `S(K)^b` is then the group of points on which every
character has valuation zero. That is the Library's
`characterValuationKernel (MaximalUnramified.valuation F) S_K`, whose
defining condition `v (χ s) = 1` is the multiplicative form of
`ω(χ(s)) = 0`.

The statement quantifies over every `B`, not only the datum constructed in
Chapter 9. The published statement's Markdown gives the reason this is
sound: `B` is `ω`-compatible, so its apartment class is unique by KP
Proposition 6.2.6 (Library `omegaCompatibleApartmentUniqueness`), and its
maximal split torus is unique up to `G(F)`-conjugacy. The Chapter 9
construction applies to every maximal `F`-split torus, in particular to
`B.S`. Proposition 6.2.6 identifies the apartment class of `B` with the
class of Theorem 9.6.5 for `B.S`. So for an arbitrary `B` the map `a` is the
inverse of the isomorphism `z ↦ ϕ^z` of §9.6.6, followed by the inclusion of
`A(B.S) = A^Γ` into `A`. Since §9.6.6 identifies the affine roots, clause 7
holds for this `a`. Clause 8 concerns the torus `B.S` of `B` itself, whose
apartment is `B(G_K)^Γ_{B.S}`. The statement only asserts that some affine
map exists.

Provenance is derived. The statement combines the cited assertions on the
Library's existing quotients, actions and Galois data. The Library proof
route for the published statement already constructs `e` as
`UnramifiedBuildingDescent.descentMap`. Its lemma `descentMap_apartment`
gives `e (B.apartmentMap w) = C.apartmentMap (descentPoint w)`, where
`descentPoint w` is a Galois-fixed point of the apartment of `C`. A proof of
clause 3 must show that `descentPoint` is affine, and clause 4 follows from
the fixedness of `descentPoint` through `action_smul` and
`action_apartmentMap`. A proof of clause 8 must show that the image of
`S(L)^1` acts trivially on the points `descentPoint w`.

## Proved lemma

`unramifiedBuildingDescentStatement_of_apartmentDescent` proves
`UnramifiedApartmentDescentStatement.{u} → UnramifiedBuildingDescentStatement.{u}`.
The proof applies the hypothesis to the same `F`, `G`, `hG` and `B`, and
discards `a` and clauses 3, 4, 7 and 8.

## Scope and consumers

Nothing here proves the statement or any of the cited source results. The
construction of integral models for KP Axioms 4.1.20 and 4.1.22 (task
`cd2ad671-3edf-4905-a0e2-e7aa2b160b91`) needs clauses 3, 4, 7 and 8. Clause 3
carries each nonempty bounded subset of a chart of `B` to one of `C`, where
the models over the integers of `L` are constructed. Clause 4 makes the
integral points of those models Galois-stable, so they descend to `𝒪[F]`.
Clause 7 carries each facet of `B` into one facet of `C`, which gives the
facet constancy of Axiom 4.1.20(1) from its counterpart over `L`
(`UnramifiedZeroFixerAffineRootStatement`). Clause 8 supplies the hypothesis
of `UnramifiedTorusClauseStatement` that `S(L)^1` fixes the chosen subset over
`L`, which gives the integral torus data of the model family.
