# The groups `G(K)_{x,r}` of a quasi-split group over `K = F^ur`

This module defines the subgroups `G(K)_{x,r}` of Kaletha–Prasad Definition
7.3.3(3) at the constant concave function `f = r`. They are defined for building
data over the maximal unramified extension `K` of a nonarchimedean local field `F`,
when the centralizer `Z = Z_G(S)` of the maximal `K`-split torus is a torus. KP §7.2
(PDF p. 276) covers this case: "When G is quasi-split, then Z = T is a maximal
torus". The torus part `Z(K)_r` is the published `localTorusFiltration`. The module
also proves the basic API: monotonicity, the generators, and the form as a
supremum. It proves no other property of these groups.

## Sources

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- §7.2, printed pp. 245–246 / PDF pp. 276–277: Definition 7.2.1
  (commutator-friendly filtrations), the quasi-split case `Z = T`, Definition
  7.2.2 (functorial filtrations of tori), properties (1) and (2), and Lemma
  7.2.3.
- Definition 7.3.3 and Remarks 7.3.4–7.3.5, printed p. 247 / PDF p. 278: the
  blocks `U_{a,x,f} = U_{a,x,f(a)} · U_{2a,x,f(2a)}`, the group `G(k)♯_{x,f}`
  they generate, and `P_{x,f} = G(k)_{x,f} = G(k)♯_{x,f} · Z(k)_{f(0)}`.
  Remark 7.3.5 says that `Z(k)_{f(0)}` depends on the chosen filtration of
  `Z(k)`.
- Fact 7.3.8, printed p. 248 / PDF p. 279: translation invariance of
  `G(k)♯_{x,f}`. This module neither uses nor formalizes it.
- Definition 2.5.13, printed p. 90 / PDF p. 121: the Iwahori subgroup
  `T(K)^0`, the image of `T(L)_b` under the norm, for a finite Galois splitting
  field `L`.
- Appendix B, Definition B.10.8, printed p. 690 / PDF p. 721: the minimal
  congruent filtration `T(K)^{mc}_r`.

The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) were
checked:

- PDF p. 33 makes AS 5 a standing hypothesis of Chapter 7, known in the
  quasi-split case. It also corrects the proof of Lemma 7.1.4 and adds
  Proposition 7.3.12(6).
- PDF p. 50 clarifies that `R` in Definition B.10.8(2) is an induced torus and
  adds B.10.8(4), `T(k)^{mc}_r = T(K)^{mc}_r ∩ T(k)`.

Neither page changes Definitions 7.2.2 or 7.3.3, properties (1) and (2), or
Lemma 7.2.3.

## Setting and binder convention

- `F : Type u` is a nonarchimedean local field (`Field`, `ValuativeRel`,
  `TopologicalSpace`, `IsNonarchimedeanLocalField`) of any characteristic, in
  an arbitrary universe. There is no tameness, residue-characteristic,
  splitness or rank hypothesis.
- `K = UnramifiedClosure F`, the Library's maximal unramified extension, which
  is `LocalGalois.Separable.inertiaFixedField F`.
- `H` is a group scheme over `Spec K` with `[IsAffineHom H.X.hom]`, and
  `B : MaximalUnramified.BuildingData F H`, which is
  `IntegerValuationBuildingData (MaximalUnramified.valuation F) H`. Its fields
  are the maximal split torus `B.S`, the inclusion `B.i`, the apartment data
  `B.apartment`, and the centralizer `B.centralizer` with `j : Z → G`.

**Convention.** Besides `B`, the only binder is

```
(hZ : IsTorus B.centralizer.Z)
```

Here `IsTorus` is `Langlands.GroupScheme.IsTorus`, the field version. Every
declaration below takes `B` and then `hZ`, in that order. All declarations are
in namespace `Langlands.Geometry.Building.MaximalUnramified.BuildingData`, so
dot notation `B.moyPrasad hZ x r` works.

- `centralizerTorus B hZ` is `B.centralizer.Z` viewed as a `CommGroupScheme`.
  Its commutativity is the Library theorem `IsTorus.isCommMonObj hZ`. Since
  `IsCommMonObj` is a proposition, this involves no choice, and
  `(B.centralizerTorus hZ).toGrp = B.centralizer.Z` holds by `rfl`
  (`centralizerTorus_toGrp`).
- The instance `centralizerTorus_isAffine` shows that this scheme is affine:
  `j` is a closed immersion (`B.centralizer.isClosedSubgroup`) into the affine
  scheme `H`, and `isAffine_of_isAffineHom` applies. This is the argument of
  the private instances of the `F`-level modules.

Callers may instead have a torus `T` with its own commutative structure,
`[IsAffine T.X.left]`, `hT : IsTorus T.toGrp` and an isomorphism
`e : T.toGrp ≅ B.centralizer.Z`. They get `hZ` as `IsTorus.of_iso e.symm hT`
(module `Langlands.GroupScheme.Torus.MaximalTransport`), and
`centralizerTorusFiltration_eq_map_iso` below identifies the two filtrations.
No binder supplies the groups, the torus filtration or any of their
properties.

## Definitions

- `centralizerTorusFiltration B hZ r : Subgroup (rationalPoints B.centralizer.Z)`
  is KP's `Z(K)_r = T(K)_r` for `r : ℝ≥0`. It is defined as the published
  `localTorusFiltration F (B.centralizerTorus hZ) hZ r` (statement
  `centralizerTorusFiltration_eq`, by `rfl`). No second filtration of tori is
  introduced.
- `centralizerTorusImage B hZ r : Subgroup (rationalPoints H)` is the image
  `j(Z(K)_r)` under `rationalPoints.map B.centralizer.j`.
- `moyPrasad B hZ x r : Subgroup (rationalPoints H)`, for `x : B.Apartment` and
  `r : ℝ≥0`, is `G(K)_{x,r}`. It is defined as
  `B.centralizerTorusImage hZ r ⊔ B.apartment.sharpFiltration x (fun _ => (r : ℝ))`.

  The second term is the Library's `G(K)♯_{x,r}` (module
  `KPRealDepthSubgroups`). It is the subgroup generated by the blocks
  `U_{b,x,r} · U_{2b,x,r}` over all relative roots `b`, where `U_{2b} = 1` when
  `2b` is not a root (Remark 7.3.4). By `sharpFiltration_eq_iSup` it equals
  the subgroup generated by the `U_{b,x,r}` for all relative roots `b`,
  divisible ones included.

KP write `P_{x,f} = G(k)♯_{x,f} · Z(k)_{f(0)}` as a product. At `f = r` we have
`f(0) = r`. Here `G(K)_{x,r}` is defined as the subgroup generated by the two
factors, their supremum in the subgroup lattice. This module does not prove
that the generated subgroup equals the set of products. That would need
`Z(K)_r` to normalize `G(K)♯_{x,r}`, and the definition does not depend on it.
The same choice is made at the `F` level by
`ParahoricBuildingData.CentralizerFiltration.moyPrasad` (module
`KPMoyPrasadFiltration`), which this definition mirrors over `K`.

## Proved API

For the torus part:

- `centralizerTorusFiltration_antitone`, from `localTorusFiltration_antitone`.
- `centralizerTorusFiltration_zero`: for every finite Galois splitting field
  `E` of `Z` inside the separable closure, `Z(K)_0` is
  `torusNormIwahori K E (intermediateValuation F E) (B.centralizerTorus hZ)`.
  This is `localTorusFiltration_zero`.
- `iInf_centralizerTorusFiltration_eq_bot` (the filtration is separated) and
  `centralizerTorusFiltration_le_characterValuationKernel`.
- `centralizerTorusFiltration_eq_map_iso`: for every presentation
  `e : T.toGrp ≅ B.centralizer.Z` as above,
  `Z(K)_r = (localTorusFiltration F T hT r).map (rationalPoints.map e.hom)`.
  The proof applies `map_localTorusFiltration_le` to `e.hom` and `e.inv`,
  viewed as morphisms of commutative group schemes (`Additive.ofMul`), and
  uses `e.inv ≫ e.hom = 𝟙`. `centralizerTorusImage_eq_map_iso` is the same
  statement for the image in `G(K)`.
- `centralizerTorusImage_antitone`.

For `G(K)_{x,r}`:

- `moyPrasad_eq_sup` (`rfl`) and `moyPrasad_eq_sup_iSup`:
  `G(K)_{x,r} = j(Z(K)_r) ⊔ ⨆ b : relativeRoots B.i, U_{b,x,r}`.
- `centralizerTorusImage_le_moyPrasad` and `map_mem_moyPrasad`: `j(Z(K)_r)`
  is contained in `G(K)_{x,r}`.
- `sharpFiltration_le_moyPrasad` and `filtration_le_moyPrasad`:
  `G(K)♯_{x,r}`, and `U_{b,x,r}` for every relative root `b`, are contained in
  `G(K)_{x,r}`.
- `moyPrasad_le_iff`: `G(K)_{x,r} ≤ Q` if and only if `j(Z(K)_r) ≤ Q` and
  `U_{b,x,r} ≤ Q` for every relative root `b`. So `G(K)_{x,r}` is the least
  subgroup containing all the generators.
- `moyPrasad_antitone`: `r ≤ s` implies `G(K)_{x,s} ≤ G(K)_{x,r}`. The proof
  combines the antitone torus image with `filtration_antitone` for each root
  group.

## The torus filtration and KP Lemma 7.2.3

KP Lemma 7.2.3 says that every functorial filtration of tori (Definition 7.2.2)
with properties (1) and (2) of §7.2 is commutator friendly. The lemma needs only
these three hypotheses. KP's own instance is the minimal congruent filtration
of Appendix B. The Library's `localTorusFiltration` is a different filtration.
A separate statement task (S1 of Task 5647's decomposition) states the lemma
for it over `K`. This section shows how each
hypothesis applies to `localTorusFiltration`, and where the Library lacks a
result.

- **Functoriality (Definition 7.2.2).** This is `map_localTorusFiltration_le`:
  for every morphism `f : T ⟶ U` of tori over `K`, `f(T(K)_r) ⊆ U(K)_r`.
- **Property (2): the induced-torus formula at `r > 0`.** This is
  `mem_localTorusFiltration_of_induced`. For an induced torus `T` and
  `r > 0`, `t ∈ T(K)_r` if and only if
  `r ≤ ω(χ(t) − 1)` for every character `χ` of `T` over the separable
  closure. Here `ω` is `algebraicExtensionAddValuation F` normalized by the
  order of `F`.
- **Property (1): the zero term is the Iwahori subgroup `T(K)^0` of
  Definition 2.5.13.** By `localTorusFiltration_zero`, the zero term is
  `torusNormIwahori K E (intermediateValuation F E) T` for every finite Galois
  splitting field `E`, the image under the norm of the character-valuation
  kernel of `T(E)`. The Library takes this group as `T(K)^0` by definition:
  `UnramifiedZeroDatum.torusIwahori` (module `KPZeroSubgroups`) is
  `torusNormIwahori`. That definition represents KP's `T(L)_b` by the
  character-valuation kernel, which is the description of `ker(ω_T)` in KP
  Proposition 2.5.8. **No Library result proves that this kernel is the
  maximal bounded subgroup `T(L)_b`.** `SplitTorusValuation.md` says so
  explicitly: "Maximal boundedness is not formalized". So property (1) holds
  only in the sense that the Library's `T(K)^0` is defined as the norm
  Iwahori. No Library theorem identifies the zero term with KP's `T(K)^0` as
  defined through maximal bounded subgroups.

`localTorusFiltration` is **not** KP's minimal congruent filtration
`T(K)^{mc}_r` of Definition B.10.8. That filtration is generated, for
`0 < r < 1`, by `T^0(M)` and the images of the standard filtrations of
induced tori, and is extended to `r ≥ 1` by congruence subgroups. The Library
filtration is instead the norm Iwahori intersected, at positive depth, with a
geometric-character congruence condition. The two filtrations agree at
`r = 0` (both are `T(K)^0`, subject to the caveat above). This module asserts
no comparison of them at positive depth. Lemma 7.2.3 does not need one: its
proof uses only functoriality, (1) and (2).

## Provenance and credit

`moyPrasad` is the source definition, KP Definition 7.3.3(3) at `f = r`, with
`Z(K)_• = T(K)_•` taken as the Library filtration. `centralizerTorus`,
`centralizerTorusFiltration` and `centralizerTorusImage` are the internal
names this needs. The transport lemmas `*_eq_map_iso` are internal
consequences of functoriality, for callers that present `Z` through another
torus.

The torus filtration `localTorusFiltration` (module
`KPLocalTorusCharacterFiltration`) was developed from the shared draft
`KPLocalTorusCharacterFiltration` by Worker 1443 (previous instance). This
module only applies it to the centralizer `Z`.
