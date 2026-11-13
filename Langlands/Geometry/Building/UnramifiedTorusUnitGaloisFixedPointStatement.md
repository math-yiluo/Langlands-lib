# A Galois-fixed building point over `F^ur` fixed by `S(K)^1`

The module states the proposition
`Langlands.Geometry.Building.UnramifiedTorusUnitGaloisFixedPointStatement.{u}`. It is the
first step of Kaletha–Prasad's proof of Proposition 9.3.4: there is a point of the building
of `G` over the maximal unramified extension that is fixed by the Galois group and by the
bounded points of a given maximal split torus. This is a derived statement, with no proof in
this module. The module adds only this proposition definition and a private instance. The
instance gives affineness of the base-changed group from affineness of `G`.

## Exact scope

For every `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]` and
`[IsNonarchimedeanLocalField F]`, every `G : GroupScheme (Spec (CommRingCat.of F))` with
`hG : IsConnectedReductive G`, every `S : CommGroupScheme (Spec (CommRingCat.of F))`, and
every homomorphism `iS : S.toGrp ⟶ G` with `IsMaximalSplitTorus iS`, write
`K = inertiaFixedField F` and `Γ = K ≃ₐ[F] K`. Equip `baseChanged F K G` with the affineness
coming from `hG.isAffineHom`. Then there exist

* `C : MaximalUnramified.BuildingData F (baseChanged F K G)`,
* a group homomorphism `ρ : Γ →* Equiv.Perm C.ReducedBuilding`, and
* a point `y : C.ReducedBuilding`,

with the following three properties.

1. Semilinearity: for every `σ : Γ`, every `g : rationalPoints (baseChanged F K G)` and every
   `z : C.ReducedBuilding`, `ρ σ (g • z) = rationalConjugate F K G σ g • ρ σ z`.
2. Galois invariance: `ρ σ y = y` for every `σ : Γ`.
3. `IsFixedByUnramifiedTorusUnits F iS y`. This means that every point `t` of
   `S_K(K) = rationalPoints (baseChanged F K S.toGrp)` in
   `characterValuationKernel (MaximalUnramified.valuation F) (baseChanged F K S.toGrp)` fixes
   `y` after it is mapped to `G(K)` by `rationalPoints.map` of the base change of `iS` along
   `baseMap F K`.

The universe `u` is arbitrary, and equal and mixed characteristic are included. The
building data `C`, the action `ρ` and the point `y` are all asserted to exist; none is
supplied.

## Library objects and KP notation

The source is Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. It is read together with
the authors' corrections dated 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. Locators give printed pages
and the one-based page numbers of the retained PDFs.

KP Chapter 9 works over a field `k` with a discrete valuation, Henselian ring of integers and
perfect residue field. They write `K` for a maximal unramified extension and identify
`Γ = Gal(K/k)` (Chapter 9 opening, printed p.323 / PDF p.354). A nonarchimedean local field
satisfies these hypotheses. The identifications are:

* `k` is `F`. `K` is `inertiaFixedField F`, the maximal unramified extension of `F` inside
  the chosen separable closure. `Γ` is the group `K ≃ₐ[F] K` of `F`-automorphisms of `K`.
* The valuation of `K` is `MaximalUnramified.valuation F`, normalized and with values in
  `WithZero (Multiplicative ℤ)`.
* `MaximalUnramified.BuildingData F H` is `IntegerValuationBuildingData` for this valuation.
  It packages a maximal `K`-split torus of `H`, root-datum apartment data
  (`KPApartmentData`) for the order of the valuation, and a compatible centralizer datum.
  `C.ReducedBuilding` is the quotient of `G(K) × A` built from these data, with its
  `G(K)`-action. For data coming from a valuation of the root datum of the quasi-split group
  `G_K`, this quotient is the building `B(G_K)` of KP Chapter 7.
* `rationalConjugate F K G σ` is the action of `σ` on `G(K)` through the coefficients. In KP
  it is written `g ↦ σ(g)`.
* For a split torus `S_K`, `characterValuationKernel` of `S_K` is its maximal bounded
  subgroup `S(K)^1 = S(K)_b` (KP Lemma 2.6.16(4) and Remark 2.6.18, printed p.103 / PDF
  p.134).

## Source of the statement

The statement combines four passages of KP.

* Existence of `C`. By the opening of Chapter 9 (printed p.323 / PDF p.354), `G_K` is
  quasi-split by Corollary 2.3.8, and Chapters 6, 7 and 8 provide Bruhat–Tits theory for
  `G_K`. In particular `G_K` has a valuation of its root datum and the building `B(G_K)` of
  Chapter 7. Such data give an element `C` whose reduced building is `B(G_K)`.
* The action `ρ`. Proposition 7.9.5 (printed p.276 / PDF p.307) gives, for an isomorphism
  of Henselian valued fields `f : k₁ → k₂` and an isomorphism `f_G` of reductive groups
  covering `f`, an isomorphism of buildings `f_B` with `f_B(g · x) = f_G(g) · f_B(x)`. As
  KP §9.2.1 (printed p.325 / PDF p.356) records, applying this with `f = σ ∈ Γ` and the
  `σ`-twist of `G_K` endows `B(G_K)` with an action of `Γ` by building automorphisms with
  `σ(g · x) = σ(g) · σ(x)`. Transporting this action to `C.ReducedBuilding` gives `ρ` and
  item 1.
* Finite orbits. The corrected second paragraph of p.326 (corrections PDF p.39) shows that
  every `Γ`-orbit in `B(G_K)` is finite: choose any apartment through the point and its
  corresponding maximal `K`-split torus `T`. There is a finite Galois subextension
  `k'/k` of `K/k` over which `T` is defined and split. The apartment is fixed pointwise by
  `Gal(K/k')`, so the orbit factors through `Gal(k'/k)`. This does not require a
  `Γ`-stable apartment or a special `k`-torus.
* The fixed point. The paragraph added at the end of §9.2.1 (corrections PDF p.39) shows that
  a bounded `Γ`-stable subgroup of `G(K)` has a `Γ`-fixed point among its fixed points in
  `B(G_K)`. The fixed set is nonempty, closed and convex (Corollary 4.2.14, Proposition
  4.2.18, Proposition 4.2.7 and Lemma 1.1.11), and the Fixed Point Theorem 1.1.15 is applied
  to the closed convex hull of a finite `Γ`-orbit in it.

The first paragraph of the proof of Proposition 9.3.4 (printed p.332 / PDF p.363) applies
this to `S(K)^1`. KP note that `S(K)^1` is `Γ`-stable, since `S` is a `k`-torus, and by
Proposition 4.2.13 its action on `B(G_K)` is bounded. KP conclude: "So there exists a point,
say x, of B(G_K) that is fixed under Γ and S(K)^1." This point gives `y`, item 2 and item 3.

## Formulation choices and limits

* The building data `C` are existentially quantified. The Library type
  `IntegerValuationBuildingData` asserts no inhabitance, and it records fewer conditions
  than KP's construction theorems. The statement claims only that some such data carry the
  required action and point.
* `ρ` is required only to be a group homomorphism to permutations that is semilinear for
  `rationalConjugate`. Compatibility with apartments, the polysimplicial structure,
  isometry and continuity are not recorded. They are not needed by the intended consumer.
* The statement fixes one maximal `F`-split torus `S`, as in the proof of Proposition 9.3.4.
  The general claim for every bounded `Γ`-stable subgroup is not formalized; the
  conclusion retains only fixation by the explicitly defined character-valuation kernel.
* No `F`-torus `T` with `T_K` maximal `K`-split is supplied or produced. The existing Library
  Galois action `KPApartmentData.galoisQuotientAction` requires Galois-stable apartment data
  for such a torus, that is, a special `F`-torus in the sense of KP §9.2.2. Their existence is
  Proposition 9.3.4 itself, whose Library form `SpecialTorusIntegralModelStatement` is derived
  from `SpecialTorusBoundedModelStatement`. This statement avoids that circularity by asking
  for the action directly.

## Intended use

Together with `IntegralModel.UnramifiedSmoothModelDescentStatement` and the five vertex
inputs of `Langlands.BruhatTits.IntegralModels.exists_smoothFullModel_of_vertexInputs`, this
statement implies `Langlands.Geometry.Building.SpecialTorusBoundedModelStatement`. The model
over `O` is the full model at `y`. The published
`exists_descent_of_fixedPoint_integralPoints` descends it to `𝒪[F]`. Its unramified integral
points are `G(K)^1 ∩ G(K)_y`. They contain the image of `S(K)^1` by item 3. They also contain
`A(K)^1` for the maximal `K`-split torus of the apartment through `y`, by
`torusUnitApartmentFixation`. This deduction is a check carried out outside this module and is
not part of it.

Worker 25 wrote the original Lean/Markdown draft for Task 6196
(`06c39422-c7bd-4529-be25-02182885ffaa`). Worker 255 checked its source correspondence and
Library interfaces and clarified this Markdown for Task 6412
(`47b6a973-b540-4c42-a3eb-9012b58b50ed`).
