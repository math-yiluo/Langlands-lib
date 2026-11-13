# A smooth model containing the bounded points of two split tori

The module states the proposition
`Langlands.Geometry.Building.SpecialTorusBoundedModelStatement.{u}`. It is the building
input of Kaletha–Prasad's proof of Proposition 9.3.4, stated only through bounded groups
of rational points, without integral tori. This is a derived statement, with no proof in
this module. The module
`Langlands.Geometry.Building.SpecialTorusIntegralModelReduction` derives the Library
statement `SpecialTorusIntegralModelStatement` from it.

## Exact scope

For every `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]` and
`[IsNonarchimedeanLocalField F]`, every
`G : GroupScheme (Spec (CommRingCat.of F))` with `IsConnectedReductive G`, every
`S : CommGroupScheme (Spec (CommRingCat.of F))`, and every homomorphism
`iS : S.toGrp ⟶ G` with `IsMaximalSplitTorus iS`, there exists
`M : IntegralModel ↥𝒪[F] F G` with the following three properties.

1. `M.IsSmooth`: the structure morphism of `M.group` is smooth. The `IntegralModel`
   structure already supplies affineness, flatness, local finite type and a generic
   identification `M.genericIso` with `G`.
2. Write `K = inertiaFixedField F` and `v = MaximalUnramified.valuation F`. The subgroup
   `characterValuationKernel v (baseChanged F K S.toGrp)` of the `K`-points of `S_K`,
   mapped to `G(K)` by `rationalPoints.map` of the base change of `iS` along
   `baseMap F K`, is contained in `M.baseChangeUnramified.integralPoints`.
3. There exist a commutative group scheme `A` over `Spec K` and a homomorphism
   `iA : A.toGrp ⟶ baseChanged F K G` with `IsMaximalSplitTorus iA` such that the image of
   `characterValuationKernel v A.toGrp` under `rationalPoints.map iA` is contained in
   `M.baseChangeUnramified.integralPoints`.

The universe `u` is arbitrary, and equal and mixed characteristic are included. There is no
connectedness requirement on the special fibre of `M`, and no supplied model, building,
point or torus.

## Library objects and KP notation

The source is Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. Locators give printed
pages and the one-based page numbers of the retained PDF.

KP work over a field `k` with a discrete valuation `ω`, Henselian ring of integers `o` and
perfect residue field `f`. They write `K` for a maximal unramified extension of `k`, `O`
for its ring of integers and `ω` again for the extended valuation (opening of Chapter 4,
printed p.157 / PDF p.188). A nonarchimedean local field satisfies these hypotheses. The
identifications are:

* `k` is `F`, and `o` is `𝒪[F]`.
* `K` is `inertiaFixedField F`, the fixed field in `SeparableClosure F` of the inertia
  subgroup of `Gal(SeparableClosure F / F)`. This is the maximal unramified extension of
  `F` inside the chosen separable closure.
* `O` is `fixedFieldIntegers F`, the valuation subring of `K`.
* The valuation `ω` of `K` is `v = MaximalUnramified.valuation F`, with values in
  `WithZero (Multiplicative ℤ)`. It is normalized and written multiplicatively, so
  `ω(x) = 0` becomes `v x = 1`.
* For a group scheme `H` over `K`, `characterValuationKernel v H` (from
  `Langlands.Geometry.Building.KPZeroSubgroups`) is the subgroup of `H(K)` of points `h`
  with `v (χ h) = 1` for every `K`-rational character `χ` of `H`.

For a connected reductive group `H` over `K`, KP Lemma 2.6.16(4) (printed p.103 / PDF
p.134) gives `H(K)^1 = {h ∈ H(K) | ω(χ(h)) = 0 for all χ ∈ X^*(H)}`. So `H(K)^1` is
`characterValuationKernel v H`. For a torus, Remark 2.6.18 (same page) says that `H(K)^1`
is the maximal bounded subgroup `H(K)_b`; the Library docstring of
`characterValuationKernel` cites Proposition 2.5.8 for this description. In particular
items 2 and 3 concern the maximal bounded subgroups `S(K)^1` and `A(K)^1` of the split
tori `S_K` and `A`.

`M.baseChangeUnramified` is the base change of `M` along `𝒪[F] → O`, with generic fibre
identified with `baseChanged F K G`. Its `integralPoints` are the image of its `O`-points
in `G(K)`.

## Comparison with the proof of KP Proposition 9.3.4

The proof of Proposition 9.3.4 (printed p.332 / PDF p.363) finds a point `x` of the
building `B(G_K)` that is fixed by `Γ = Gal(K/k)` and by `S(K)^1`. It then works with the
smooth affine `o`-group scheme `𝒢^1_x`. Read its appeal to §9.2.1 together with the
corrections dated 1 November 2024 (registered as `kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF p.39). They
show that `Γ` has finite orbits on `B(G_K)` and that every bounded `Γ`-stable subgroup of
`G(K)` fixes some `Γ`-fixed point of `B(G_K)`. The model `M` of the residual is this `𝒢^1_x`:

* Axiom 4.1.2 (printed p.158 / PDF p.189) defines `G(K)^1_x` as the stabilizer of `x` in
  `G(K)^1`. Axiom 4.1.20 (printed p.163 / PDF p.194), applied over `K` with `Ω = {x}`,
  gives a smooth affine `O`-group scheme `𝒢^1_x` with generic fibre `G_K` and
  `𝒢^1_x(O) = G(K)^1_x`.
* Section 9.2.5 (printed pp.327–328 / PDF pp.358–359) descends `𝒢^1_x`, for `Γ`-fixed
  `x`, to a smooth affine `o`-group scheme with generic fibre `G`. Its base change to `O`
  is the `O`-group scheme `𝒢^1_x`. Taking `M` to be this descent gives item 1, and
  `M.baseChangeUnramified.integralPoints` is `G(K)^1_x`.
* The proof of 9.3.4 records `S(K)^1 ⊂ G(K)^1_x`: `S(K)^1` lies in `G(K)^1` by Lemma
  2.6.16(2) and fixes `x`. This is item 2.
* Choose an apartment of `B(G_K)` containing `x`, and let `A` be the corresponding maximal
  `K`-split torus of `G_K` (Axiom 4.1.1, printed p.157 / PDF p.188). Let `Z` be its
  centralizer. By Axiom 4.1.4 (A1) (printed p.159 / PDF p.190), `Z(K)` acts on the
  apartment by translations and its maximal bounded subgroup `Z(K)_b` acts trivially. The
  group `A(K)^1` is bounded (Remark 2.6.18), so it lies in `Z(K)_b` and fixes `x`. It lies in
  `G(K)^1` by Lemma 2.6.16(2). Hence `A(K)^1 ⊂ G(K)^1_x`, which is item 3.

Items 2 and 3 are the hypotheses of Proposition B.2.4 (printed p.656 / PDF p.687) for the
smooth affine group scheme `𝒢^1_x` and the tori `S` and `A`; the proof of 9.3.4 applies
B.2.4 to `S`. Item 3 also follows from Axiom 4.1.20(3), which supplies a closed `O`-split
torus in `𝒢^0_x` with generic fibre `A`, together with Lemma B.2.3.

## Formulation choices and limits

The residual replaces the closed integral tori of `SpecialTorusIntegralModelStatement` by
their bounded points, and it drops the connected special fibre. Both are recovered in
`Langlands.Geometry.Building.SpecialTorusIntegralModelReduction`. The passage from bounded
points to closed split integral tori is the split-torus case of KP Lemma B.2.3 and
Proposition B.2.4 (printed pp.655–656 / PDF pp.686–687), proved in
`Langlands.GroupScheme.IntegralModel.SplitTorusBoundedPoints`. The passage to the relative
identity component, which gives the connected special fibre, is proved in
`Langlands.GroupScheme.IntegralModel.SpecialTorusNeutralModel`.

The point `x`, the building, `Γ`-invariance and the identification of `M` with a
Bruhat–Tits group scheme are not recorded. The statement asks only for the two containments
of bounded groups. The module introduces only this proposition definition.

The Lean statement was drafted by Worker 5707 for Task 5707
(`f502c3c7-c095-4c74-bf82-ad8ffb916f57`, shared draft revision 2). Worker 25 revised this
Markdown for publication.
