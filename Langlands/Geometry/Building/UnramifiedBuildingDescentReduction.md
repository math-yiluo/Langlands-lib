# Reduction of unramified building descent to focused Kaletha–Prasad inputs

This module reduces the published target
`Langlands.Geometry.Building.UnramifiedBuildingDescentStatement` to six published statements
and three new Prop-valued statements. It proves the reduction.

- `Langlands.Geometry.Building.MaximalUnramifiedApartmentInjectiveStatement` (new):
  the apartment embeds in the reduced building over `K` (KP Proposition 7.6.3 and
  Remark 7.6.5 over `K`).
- `Langlands.Geometry.Building.UnramifiedGaloisFixedBuildingPointStatement` (new):
  Galois-fixed points of the building over `K` are `G(F)`-translates of fixed apartment
  points (KP §9.2.3, Theorem 9.2.7, Proposition 9.3.4 and §9.3).
- `Langlands.Geometry.Building.UnramifiedSpecialPointDescentStatement` (new): special
  points descend (KP Proposition 9.9.2).
- `Langlands.Geometry.Building.UnramifiedBuildingDescentReductionStatement` and its proof
  `Langlands.Geometry.Building.unramifiedBuildingDescentReduction`.

None of the three new statements is proved here. All statements are universe
polymorphic. They range over every `F : Type u` with `Field F`, `ValuativeRel F`,
`TopologicalSpace F` and `IsNonarchimedeanLocalField F`, in equal and mixed
characteristic. They impose no splitness, quasi-splitness, tameness, rank or residue
restriction on `G`.

Throughout, `K` is the Library's maximal unramified extension `inertiaFixedField F`,
definitionally `UnramifiedClosure F`. `MaximalUnramified.valuation F` is its normalized
integer-valued valuation, and `Aut(K/F)` is `inertiaFixedField F ≃ₐ[F] inertiaFixedField F`.
Scalar extension is the existing base change along `algebraBaseMap F K`. For an `F`-torus
`T` with `iT : T.toGrp ⟶ G`, write `T_K` and `iT_K` for the scalar extensions. The affine
instance of `G_K` is supplied by pullback. The monomorphism instances come from the
maximal-split-torus hypotheses through `mono_of_isMaximalSplitTorus`.

The module also uses two helper modules written by Worker 4341 for this task:

- `Langlands.Geometry.Building.UnramifiedOmegaGaloisStable`, with
  `MaximalUnramified.galoisStable_of_isOmegaCompatible`: a class over `K` satisfying V 6 on
  `T_K`, for a closed `F`-torus `T` with `T_K` maximal `K`-split, is `Aut(K/F)`-stable
  (KP §9.2.1);
- `Langlands.Geometry.Building.UnramifiedFiltrationSharpFixer`, with
  `filtration_le_comap_sharpFixer_of_torusFieldRestriction`: a depth-zero root
  filtration of the descended point lies in the preimage of the sharp fixer of the point
  over `K`.

## `MaximalUnramifiedApartmentInjectiveStatement`

For every `F` as above, every group `H` over `Spec K` with `IsAffineHom H.X.hom`, and every
`C : MaximalUnramified.BuildingData F H`, the map `C.apartmentMap` from the apartment to
the reduced building is injective. The data `C` consist of a connected reductive `H`, a
maximal `K`-split torus, an equipollence class of valuations of the root datum
normalized by the order of `MaximalUnramified.valuation F`, the actual centralizer, and
V 6. Over a local field this injectivity follows from the apartment axioms (KP
Proposition 7.6.3 and Remark 7.6.5). This statement asserts it over `K`, where KP
Chapters 6–7 apply to the quasi-split group `H` over the henselian, discretely valued
field `K`.

## `UnramifiedGaloisFixedBuildingPointStatement`

The binders are:

- a connected reductive `G` over `Spec F` (`hG`);
- a maximal split torus `iS : S.toGrp ⟶ G`;
- an `F`-torus `iT : T.toGrp ⟶ G` and `f : S ⟶ T` with
  `CommGroupScheme.groupHom f ≫ iT = iS`, so `S` lies in `T`;
- `hiT`: `iT_K` is a maximal split torus of `G_K`, so `T` is a special torus (KP
  Proposition 9.3.4);
- `D : KPApartmentData iT_K ω`, with `ω` the order of `MaximalUnramified.valuation F`, and
  a centralizer datum `C` with V 6 for `D` and `C`;
- `hD : KPApartmentData.GaloisStable F K iT D`.

The conclusion: every `y : D.ReducedBuilding` fixed by
`KPApartmentData.galoisQuotientAction F K iT D hD σ` for every `σ` equals
`rationalExtend F K G g • D.apartmentMap x` for some `g : G(F)` and some `x : D.Apartment`
with `RootFunctionFamily.galoisAction F K T G σ x.val = x.val` for every `σ`. The
`rationalExtend` image is ascribed (`show`) to the rational points of
`(GroupScheme.baseChange (algebraBaseMap F K)).obj G`, as in
`UnramifiedValuationDescentStatement`.

This is the content of KP Theorem 9.2.7, `B(G) = B(G_K)^Γ`, together with §9.3:
`B(G)` is the union of the `G(F)`-translates of `A(S)`, and `A(S)` is the set of
`Γ`-fixed points of `A(T_K)` for a special torus `T ⊇ S`. The hypothesis that `T`
contains a maximal `F`-split torus is needed. For an anisotropic unramified `T` with
`T_K` maximal `K`-split, `A(T_K)^Γ` can be a single point.

## `UnramifiedSpecialPointDescentStatement`

The binders are those of `UnramifiedValuationDescentStatement`: `G`, `hG`, `iS`, `hiS`,
`T`, `iT`, `f`, the factorization, `hiT`, `hE`, `D`, `C` and V 6. The lets `fixed` and `φ`
are copied from it verbatim. Then for every `DS : KPApartmentData iS (localFieldOrder F)`
whose carrier is exactly `{φ x | fixed x}`, every fixed `x : D.Apartment` and every
`w : DS.Apartment` with `w.val = φ x`: if `D.apartmentMap x` is a special point of the
reduced building of `D` (`KPApartmentData.IsSpecialBuildingPoint`), then `w` is a special
point for `DS.affineRoots` (`AffineRootSystem.IsSpecialPoint`).

This is KP Proposition 9.9.2 (printed p. 380, PDF p. 411): a point of `B(G)` that is
special in `B(G_K)` is special in `B(G)`. KP's proof restricts the affine roots of `G_K`
vanishing at the point from `T_K` to `S`.

## `UnramifiedBuildingDescentReductionStatement`

The hypotheses, in order:

1. `UnramifiedQuasiSplitStatement` (published);
2. `QuasiSplitIntegerApartmentExistenceStatement` (published);
3. `SpecialTorusExistenceStatement` (published, KP Proposition 9.3.4);
4. `UnramifiedValuationDescentStatement` (published);
5. `ValuationBuildingApartmentAxiomsStatement` (published);
6. `ChapterSevenBuildingAxiomsStatement` (published);
7. `MaximalUnramifiedApartmentInjectiveStatement`;
8. `UnramifiedGaloisFixedBuildingPointStatement`;
9. `UnramifiedSpecialPointDescentStatement`.

The conclusion is `UnramifiedBuildingDescentStatement`.

## Constructions (namespace `UnramifiedBuildingDescent`)

- `buildingData iT hGK hiT D C h6`: the `MaximalUnramified.BuildingData` over
  `baseChanged F K G` with torus `T_K`, inclusion `iT_K`, class `D`, centralizer `C` and
  V 6 `h6`.
- `semilinearData … hD`: the `MaximalUnramified.SemilinearApartmentData` on it, for a
  Galois-stable `D`. The apartment action is `KPApartmentData.galoisAction`. Normalizer
  membership is `rationalConjugate_mem_normalizerPoints`. Normalizer compatibility is
  `KPApartmentData.galoisAction_normalizer_smul`, after identifying
  `normalizerGaloisAction` with the explicit conjugate. The root index sends `a` to
  `characterLattice.galoisRepresentation F K T σ a` (a root by `mem_roots_galois_iff`).
  Filtrations are carried by `KPApartmentData.rationalConjugate_mem_filtration_iff` at
  depth `0`.
- `semilinearData_action_apply`: its quotient action agrees pointwise with
  `KPApartmentData.galoisQuotientAction`. Write a point as `g • D.apartmentMap x`; both
  actions send it to `rationalConjugate σ g • D.apartmentMap (galoisAction σ x)`.

## The core lemma `UnramifiedBuildingDescent.exists_descent`

The section `Core` fixes `B : ValuationBuildingData G`, a predicate `fixed` on
`D.Apartment` and a map `φ : D.Apartment → RootFunctionFamily B.S G` with the following
hypotheses:

- `hcar`: the carrier of `B.apartment` is `{φ x | fixed x}`;
- `hinj`: `φ` is injective on fixed points;
- `hnorm`: normalizer compatibility. For `n ∈ N(F)` and fixed `x` there is a fixed `y` with
  `D.apartmentMap y = rationalExtend n • D.apartmentMap x` and `φ y = n • φ x`;
- `hfilt`: if `w.val = φ x`, then each depth-zero root filtration `B.filtration w a 0`
  lies in the preimage of `D.sharpFixer {x}` under `rationalExtend`.

From these it builds:

- `descentPoint w`, a chosen fixed `x` with `w.val = φ x`
  (`descentPoint_fixed`, `descentPoint_val`). It is injective (`descentPoint_injective`)
  and unique among fixed points (`descentPoint_eq`, from `hinj`).
- `descentPoint_normalizer`. Apply `hnorm` to `descentPoint w`. Uniqueness, with
  `(n • w).val = n • w.val`, identifies the resulting `y` with `descentPoint (n • w)`.
  `descentPoint_normalizer'` restates this for `buildingData`.
- `descentPoint_sharpFixer`. Use `MaximalUnramified.sharpFixer_le_comap_of_rootFiltration`
  with `hfilt` and `D.sharpFixer_le_reducedFixer`.
- `descentMap := MaximalUnramified.quotientLift B (buildingData …) descentPoint …`. It is
  equivariant along `rationalExtend` (`descentMap_smul`, from `quotientLift_smul`) and
  extends the apartment map (`descentMap_apartment`).

The four conclusions:

1. `descentMap_injective`: `MaximalUnramified.quotientLift_injective`, from the building
   axiom of `B` (hypothesis `hB`), injectivity of `descentPoint` and injectivity of
   `D.apartmentMap` (hypothesis `hK`).
2. `descentMap_smul`.
3. `descentMap_surjective_fixed`. Let `y` be fixed by every `semilinearData` action.
   By `semilinearData_action_apply` it is fixed by `galoisQuotientAction`. Hypothesis
   `hfixpt` writes it as `rationalExtend g • D.apartmentMap x` with `x` fixed. Then
   `w := ⟨φ x, _⟩ ∈ B.Apartment` by `hcar`, `descentPoint w = x` by `descentPoint_eq`, and
   `descentMap (g • B.apartmentMap w) = y`.
4. `descentMap_isSpecialPoint`. Write `z = g • B.apartmentMap w`. Special points are
   stable under translation (`KPApartmentData.IsSpecialBuildingPoint.smul`), so the image
   of `descentPoint w` is special upstairs. Hypothesis `hspec` makes `w` special for
   `B.affineRoots`. Then `isSpecialBuildingPoint_apartmentMap` and translation by `g` give
   `B.IsSpecialPoint z`.

`exists_descent` packages `buildingData`, `semilinearData`, `descentMap` and these four
facts as the existential of the target.

## Proof of `unramifiedBuildingDescentReduction`

Fix `F`, `G`, `hG` and `B`, and write `S`, `iS` for the torus of `B`.

1. `SpecialTorusExistenceStatement` gives a closed `F`-torus `T ⊇ S` with `iT_K` a maximal
   split torus of `G_K`.
2. `connectedReductiveFieldExtensionStatement` shows `G_K` is connected reductive.
   `exists_omegaCompatible`, which uses `UnramifiedQuasiSplitStatement` and
   `QuasiSplitIntegerApartmentExistenceStatement`, gives `D`, `C` and V 6 over `K` on
   `T_K`.
3. Opposite factor pairs `hE` for `iT_K` come from `rootRankOneFactorization`, as in
   `valuationApartmentAxiomsExistenceReduction`.
4. `MaximalUnramified.galoisStable_of_isOmegaCompatible` gives Galois stability `hD`.
5. `UnramifiedValuationDescentStatement` gives `DS`, `CS`, V 6 for `DS`, the carrier
   characterization, injectivity on fixed points, and normalizer compatibility.
6. `omegaCompatibleApartmentUniqueness` (KP Proposition 6.2.6) identifies `DS` with
   `B.apartment`. It uses `IsOmegaCompatible.of_centralizerDatum` to move V 6 to
   `B.centralizer`.
7. `exists_descent` concludes. Its inputs are:
   - `hfilt` from `filtration_le_comap_sharpFixer_of_torusFieldRestriction`;
   - `hK` from `MaximalUnramifiedApartmentInjectiveStatement` applied to `buildingData`;
   - `hB` from `exists_satisfiesBuildingAxiom`. This lemma extends `B` to parahoric
     data with `ParahoricBuildingData.exists_toValuationBuildingData_eq`, then applies
     `ValuationBuildingApartmentAxiomsStatement` and `ChapterSevenBuildingAxiomsStatement`;
   - `hfixpt` from `UnramifiedGaloisFixedBuildingPointStatement`;
   - `hspec` from `UnramifiedSpecialPointDescentStatement` with `DS = B.apartment`.
