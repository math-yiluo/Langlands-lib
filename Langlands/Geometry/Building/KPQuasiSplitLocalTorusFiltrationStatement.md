# KP Lemma 7.2.3 over `K = F^ur` for the torus filtration of quasi-split building data

This module states one proposition, `QuasiSplitLocalTorusFiltrationStatement`. It says that
the filtration `Z(K)_r = B.centralizerTorusFiltration hZ r` of D1 (the published torus
filtration `localTorusFiltration` of the centralizer `Z` of quasi-split building data over
the maximal unramified extension `K = F^ur`) is commutator friendly (KP Definition 7.2.1, the
property that KP Lemma 7.2.3 asserts), root compatible, and stable under conjugation by
`N(K)`. It is a statement only. Nothing is proved here.

## Sources

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`
(printed page = PDF page − 31):

- §7.2, Definition 7.2.1, printed p. 245 / PDF p. 276: a decreasing separated filtration of
  `Z(k)_b` is *commutator friendly* if `Z(k)_0 = Z(k)^0` and, for `a ∈ Φ`, `φ ∈ A`,
  `u ∈ U_a(k)*`, `u' ∈ U_{-a}(k)*` with `r := φ_a(u) + φ_{-a}(u') > 0`, the `Z`-component of
  the commutator `u'⁻¹ u u' u⁻¹` lies in `Z(k)_r` (cf. Definition 7.1.3).
- §7.2, Definition 7.2.2 and properties (1), (2), printed p. 245 / PDF p. 276: functorial
  filtrations of tori; (1) `T(k)_0` is the Iwahori group `T(k)^0` of Definition 2.5.13;
  (2) for an induced torus `T` and `r > 0`,
  `T(k)_r = {t ∈ T(k) | ω(χ(t) − 1) ≥ r for all χ ∈ X^*(T)}`.
- §7.2, Lemma 7.2.3, printed pp. 245–246 / PDF pp. 276–277: when `G` is quasi-split (so
  `Z = T` is a maximal torus), every functorial filtration satisfying (1) and (2) is
  commutator friendly. The proof reduces to rank one and to the `SL_2` and `SU_3`
  computations of the proof of Proposition 7.1.1.
- Proposition 7.1.1 and Definition 7.1.3, §7.1: the decomposition
  `u'⁻¹ u u' u⁻¹ ∈ U_{-a}(k) · Z(k) · U_a(k)` and its `Z`-component.
- Definition 7.3.3(1), printed p. 247 / PDF p. 278: the block
  `U_{a,x,f} = U_{a,x,f(a)} · U_{2a,x,f(2a)}`.

The authors' corrections of 1 November 2024 (`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) were checked. PDF p. 33
adds the assumption AS 5 at the start of Chapter 7 and notes that it is known when `G` is
quasi-split; it corrects the proof of Lemma 7.1.4 and adds Proposition 7.3.12(6). None of
this changes Definitions 7.2.1, 7.2.2, properties (1), (2) or Lemma 7.2.3.

## Setting and binder convention

The statement quantifies over:

- `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
  `IsNonarchimedeanLocalField F`, in any universe and any characteristic;
- an affine group scheme `H` over `Spec K`, `K = UnramifiedClosure F` (the Library's maximal
  unramified extension, the inertia fixed field), and
  `B : MaximalUnramified.BuildingData F H`, that is
  `IntegerValuationBuildingData (MaximalUnramified.valuation F) H`;
- D1's binder (Task 5875, `079e96f3-eb4c-4477-8a40-a1acffc66e49`, module
  `Langlands.Geometry.Building.KPLocalMoyPrasadGroups`): `hZ : IsTorus B.centralizer.Z`, which
  makes `Z = B.centralizer.Z` a torus. D1 turns it into the torus that `localTorusFiltration`
  accepts: `B.centralizerTorus hZ` is `Z` with commutativity `hZ.isCommMonObj`, and the
  instance `centralizerTorus_isAffine` makes it affine.

There is no other hypothesis. In particular the statement takes no binder that supplies a
filtration, a subgroup, or any of the three properties, and no tameness, residue
characteristic, splitness or rank assumption. The binder `hZ` is exactly the condition that
`Z` is a torus, that is, that `H` is quasi-split (KP §7.2: "When `G` is quasi-split, then
`Z = T` is a maximal torus").

The two groups are D1's definitions, imported from `KPLocalMoyPrasadGroups`:

- `Z(K)_r := B.centralizerTorusFiltration hZ r`, a subgroup of
  `rationalPoints B.centralizer.Z`. It is by definition (`centralizerTorusFiltration_eq`,
  `rfl`) the published `localTorusFiltration F (B.centralizerTorus hZ) hZ r`;
- `j(Z(K)_r) := B.centralizerTorusImage hZ r`, its image
  `(B.centralizerTorusFiltration hZ r).map (rationalPoints.map B.centralizer.j)` in
  `rationalPoints H`, with `j = B.centralizer.j`.

The statement uses no second filtration of tori. If `Z` is presented by another torus
`T` with `e : T.toGrp ≅ Z`, D1's transport lemma `centralizerTorusFiltration_eq_map_iso`
gives `Z(K)_r = e(T(K)_r)`, so the statement also applies to that presentation.

## The statement

`QuasiSplitLocalTorusFiltrationStatement` is, for all data above, the conjunction of the
following three clauses. They are the `K`-level copies of the predicates
`IsCommutatorFriendly`, `IsRootCompatible` and `IsNormalizerStable` of
`ParahoricBuildingData.CentralizerFiltration` (module
`Langlands.Geometry.Building.KPMoyPrasadFiltration`). Each copy has the same quantifier
structure, with `B` in place of `P`, `B.centralizerTorusFiltration hZ r` in place of
`Zf.filtration r` and `B.centralizerTorusImage hZ r` in place of `Zf.image r`.

1. **Commutator friendliness.** This is the commutator clause of KP Definition 7.2.1, the
   property asserted by Lemma 7.2.3. For `x : B.Apartment`, a relative root `a` of `B`,
   `u ∈ U_a(K)` (`B.rootGroup a`), `u ≠ 1`, `u' ∈ U_{-a}(K)`, `u' ≠ 1`, and `r : ℝ≥0` with
   `0 < r` and `r = x_a(u) + x_{-a}(u')` (`x.val a u + x.val (-a) u'` in `WithTop ℝ`):
   whenever `u'⁻¹ u u' u⁻¹ = v' · j(z) · v` with `v' ∈ U_{-a}(K)`, `v ∈ U_a(K)` and
   `z ∈ Z(K)`, then `z ∈ Z(K)_r`. By Definition 7.1.3 such a `z` is the `Z`-component of
   the commutator. As in the `F`-level predicate, the clause quantifies over every such
   factorization. The source shows that it exists and is unique (Proposition 7.1.1).
2. **Root compatibility.** For `x`, a relative root `a`, `r s : ℝ≥0`, `z ∈ j(Z(K)_r)` and
   `u ∈ U_{a,x,s}` (`B.filtration x a s`), the commutator `z u z⁻¹ u⁻¹` lies in
   `B.apartment.filtrationBlock x (fun _ => r + s) a`, the block
   `U_{a,x,r+s} · U_{2a,x,r+s}` of Definition 7.3.3(1). For a multipliable root the
   `2a`-factor cannot be dropped: `z` of depth `r` moves `U_{2a}` by the character `2a`,
   which gains `r` in `x_{2a}` but only `r/2` in `x_a = x_{2a}/2`.
3. **`N(K)`-stability.** For `n ∈ normalizerPoints B.i` and `r : ℝ≥0`, the image of
   `j(Z(K)_r)` under conjugation by `n` (`MulAut.conj n`) is `j(Z(K)_r)`.

Clauses 2 and 3 are not clauses of Definition 7.2.1. As at the `F` level (see the
provenance paragraph of `KPMoyPrasadFiltration.md`), they are derived properties that KP use,
sometimes tacitly. KP's proof of the commutator property of Moy–Prasad groups
(Proposition 13.2.5(4)) reduces to commutators of root-group elements; clause 2 is the
remaining commutator, of the central factor `Z(K)_r` with a root group. Clause 3 holds
because conjugation by `n ∈ N(K)` restricts to an automorphism of the torus `Z`, and the
filtration is functorial.

The other clauses of Definition 7.2.1 — a decreasing separated filtration of `Z(K)_b` with
`Z(K)_0 = Z(K)^0` — are not part of this statement. For `localTorusFiltration` the Library
already has them: `localTorusFiltration_antitone`, `iInf_localTorusFiltration_eq_bot`,
`localTorusFiltration_le_characterValuationKernel` (every term lies in `T(K)^1`) and
`localTorusFiltration_zero` (see (1) below). D1 restates them for `Z(K)_r` as
`centralizerTorusFiltration_antitone`, `iInf_centralizerTorusFiltration_eq_bot`,
`centralizerTorusFiltration_le_characterValuationKernel` and
`centralizerTorusFiltration_zero`.

**The `2r` bound is left out on purpose.** The statement does not include the sharper bound
`z ∈ Z(K)_{2r}` when `u ∈ U_{2a}(K)` or `u' ∈ U_{-2a}(K)`, the `K`-level analogue of
`IsDoubleRootCommutatorFriendly` (module `KPMoyPrasadDoubleRootStatement`). In Task 5647's
decomposition the bound is a step of the proof of S2 (Task 5892,
`15ba3e2b-27c8-46a5-bf30-f511e8ee6c4f`, the group properties of `G(K)_{x,r}`): at the `K`
level it follows from clause 1 above together with S2's other group properties, after a
translation of `x` (KP Fact 7.3.8). Putting it here would make the proofs of S1 and S2
depend on each other.

## Why Lemma 7.2.3 applies to `localTorusFiltration`

KP Lemma 7.2.3 needs a functorial filtration of tori (Definition 7.2.2) satisfying (1) and
(2). `Z(K)_r` is the published `localTorusFiltration` (module
`Langlands.Geometry.Building.KPLocalTorusCharacterFiltration`) of the torus
`B.centralizerTorus hZ`, and that filtration has these properties:

- **Functoriality** (Definition 7.2.2) is `map_localTorusFiltration_le`: every morphism
  `f : T ⟶ U` of tori over `K` maps `T(K)_r` into `U(K)_r`. The filtration is decreasing
  (`localTorusFiltration_antitone`), separated (`iInf_localTorusFiltration_eq_bot`) and
  contained in `T(K)^1` (`localTorusFiltration_le_characterValuationKernel`).
- **Property (1)** is `localTorusFiltration_zero`: for every finite Galois extension `E/K`
  inside the separable closure that splits `T`, `T(K)_0` equals
  `torusNormIwahori K E (intermediateValuation F E) T`, the image under the norm
  `T(E) → T(K)` of the character-valuation kernel of `T(E)`. That is the definition of KP's
  Iwahori group `T(K)^0` in Definition 2.5.13 (the norm image of `T(E)^b` for a splitting
  field `E`); see the docstring of `torusNormIwahori` in `KPZeroSubgroups`. Its
  independence of `E` is part of the published construction
  (`localTorusFiltrationAtSplitting_eq`).
- **Property (2)** is `mem_localTorusFiltration_of_induced`: for an induced torus `T` and
  `r > 0`, `t ∈ T(K)_r` if and only if every character `χ` of `T` over the separable closure
  `Ω` satisfies `r ≤ ω(χ(t) − 1)`, with `ω = algebraicExtensionAddValuation F Ω`.

The two depth scales agree. The torus filtration uses `algebraicExtensionAddValuation F Ω`,
normalized by the integer order of `F` (`algebraicExtensionAddValuation_base_unit`). The
apartment of `B` uses `IntegerValuation.order (MaximalUnramified.valuation F)`, whose order
restricts to the same integer order on `F`
(`MaximalUnramified.orderUnits_base_eq_fieldOrderUnits`,
`MaximalUnramified.order_base_eq_localFieldOrder`). Since `K/F` is unramified, both are the
normalized valuation of `K`.

This filtration is not KP's minimal congruent filtration of Definition B.10.8. Lemma 7.2.3
uses only functoriality, (1) and (2), so it applies to `localTorusFiltration` as well.

## Notes for the proof

These are not part of the statement. KP prove Lemma 7.2.3 by reducing to rank one
(Proposition 7.1.1) and computing in `SL_2` and `SU_3`; the Library has quasi-split rank-one
coordinates (`QuasiSplitR1RootFieldCoordinates`, `QuasiSplitR2RootUnitaryCoordinates`). The
proof also needs that `B.apartment` is the Chevalley–Steinberg class. The ω-compatibility
field `B.isOmegaCompatible` together with KP Proposition 6.2.6 (uniqueness of the
ω-compatible class; over `F` this is `OmegaCompatibleApartmentUniquenessProof`) gives it. A
version over `K` may be needed.

## Provenance

Task 5890 (`4f714327-f957-4084-b29f-8d5288f15097`) is S1 of Task 5647's decomposition
(Task 5647 proves `CentralizerFiltrationDoubleRootExistenceStatement`, KP §9.8 and Lemma
9.8.1). KP construct `Z(F)_r = Z(K)_{x,r} ∩ Z(F)` with `K = F^ur`, and the proof of Lemma
9.8.1 uses Lemma 7.2.3 for the quasi-split group `H = G_K`. The clause forms are copied from
the published `F`-level predicates so that the `F`-level reduction can use them directly.
