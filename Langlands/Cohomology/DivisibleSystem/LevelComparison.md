# Finite-level compatibility of the comparison map for `ℓ`-divisible systems of complexes

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.DivisibleSystem.AdicHyperext` (`homComplexLimitToDerived`)
and `Langlands.Cohomology.DivisibleSystem.CompatibleExt` (`derivedEval`,
`evalComplex`, `compatibleDerived`, `derivedToCompatible`). Through them it
uses `towerComplex`, `towerCochainEval` with `towerCochainEval_v`,
`towerHomComplexEval` with `towerHomComplexEval_f_apply`,
`towerHomComplexIsoLimit` with `towerHomComplexIsoLimit_hom_π`,
`linearHomComplexScIso`, `linearHomComplexHomologyAddEquiv` and
`linearHomComplexHomologyHomotopyAddEquiv`
(`Langlands.Cohomology.DivisibleSystem.TowerComplex`), `homComplexLimit` and
`homComplexSystem` (`Langlands.Cohomology.DivisibleSystem.HomSystem`), `LinearHomComplex.complex` (`Langlands.Cohomology.LinearHomComplex`)
and `precompAddEquiv`, `postcompAddEquiv`
(`Langlands.Cohomology.HyperextSecondPage`). From Mathlib it uses
`ShortComplex.mapHomologyIso`, `ShortComplex.mapCyclesIso` and their
descriptions `LeftHomologyData.mapHomologyIso_eq`,
`LeftHomologyData.mapCyclesIso_eq`, `mapCyclesIso_hom_iCycles`; the Hom complex
`CochainComplex.HomComplex` with `Cochain`, `Cocycle`, `Cochain.map`, `δ_map`,
`Cocycle.equivHomShift` (with `equivHomShift_symm_apply` and
`Cochain.rightShift_v`), `HomComplex.leftHomologyData`,
`HomComplex.homologyAddEquiv`, `CohomologyClass.mk` and
`CohomologyClass.homAddEquiv`; the shift isomorphisms
`Functor.mapHomologicalComplex ... commShiftIso` of an additive functor on
cochain complexes (identities in each degree); the localization functors `Q`,
`Qh` and `quotientCompQhIso`; `Functor.mapDerivedCategoryFactors` with its
naturality and its compatibility with shifts (`NatTrans.shift_app_comm`, from
Mathlib's instance `NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ`); and
`ModuleCat.epi_iff_surjective`.

## Conventions

`R` is a ring and `C` an `R`-linear category (abelian where derived categories
appear); `ℕᵒᵖ ⥤ C` is the category of inverse systems in `C`. For cochain
complexes `K` and `L` (indexed by `ℤ`), `Hom^•(K, L)` is the published
module-valued Hom complex `LinearHomComplex.complex R K L`, whose degree `n`
term is Mathlib's module of cochains `Cochain K L n`; the cohomology classes of
its degree `n` cycles are the elements of its degree `n` homology.
`linearHomComplexHomologyHomotopyAddEquiv R K L n` is the published
identification of this cohomology with morphisms
`K ⟶ L⟦n⟧` in the homotopy category. In sections with derived categories,
`HasDerivedCategory.{t} C` and `HasDerivedCategory` for `ℕᵒᵖ ⥤ C` are
hypotheses (no instance is constructed), and `Q` and `Qh` are the localization
functors from cochain complexes and from the homotopy category.

For `ℓ`-divisible systems `T` and `W` of cochain complexes in `C`,
`towerComplex T` is the complex of inverse systems `m ↦ T m`, and
`homComplexLimit R T W` is the inverse limit over `m` of the Hom complexes
`Hom^•(T m, W m)` (diagram `homComplexSystem R T W`, projections `limit.π`).
`evalComplex K m` is the level `m` complex of a complex `K` of inverse systems;
for `K = towerComplex T` it is `T m` by definition.

## Homology of mapped short complexes (namespace `Langlands.Cohomology`)

- `homologyπ_comp_mapHomologyIso_hom F S` (with `@[reassoc]`): for a functor
  `F` preserving zero morphisms and the left homology of a short complex `S`,
  `(S.map F).homologyπ ≫ (S.mapHomologyIso F).hom` equals
  `(S.mapCyclesIso F).hom ≫ F.map S.homologyπ`. Proof: describe both
  comparison isomorphisms by the left homology data of `S`
  (`mapHomologyIso_eq`, `mapCyclesIso_eq`) and compare the projections. The
  Library's `DerivedPlus.homologyπ_mapHomologyIso_hom` states the same for
  exact functors between abelian categories; this version assumes only the
  preservation of left homology, which Mathlib provides automatically for
  `forget₂ (ModuleCat R) AddCommGrpCat`, the case used below.

## Cocycles of the module-valued Hom complex (namespace `Langlands.Cohomology`)

- `linearHomComplexCocycle R K L n c`: for a degree `n` cycle `c` of
  `Hom^•(K, L)`, the Mathlib cocycle `Cocycle K L n` whose underlying cochain
  is the image of `c` in `Cochain K L n`; `linearHomComplexCocycle_coe`
  records this.
- `linearHomComplexHomologyHomotopyAddEquiv_homologyπ R K L n c`: the class of
  `c` is sent by `linearHomComplexHomologyHomotopyAddEquiv R K L n` to the
  homotopy class of the morphism `K ⟶ L⟦n⟧` associated with this cocycle
  (`Cocycle.equivHomShift.symm`). Proof: the published equivalence is the
  composite of the homology comparison for `forget₂`, the identity
  identification with Mathlib's `HomComplex K L`, Mathlib's
  `homologyAddEquiv` (defined by the left homology data whose cycles are the
  cocycles and whose homology is `CohomologyClass K L n`) and
  `CohomologyClass.homAddEquiv`; `homologyπ_comp_mapHomologyIso_hom`,
  naturality of `homologyπ` and the left homology data identify the class of
  `c` with `CohomologyClass.mk` of this cocycle, which `homAddEquiv` sends to
  the stated homotopy class.

## Cocycles mapped by an additive functor (namespace `Langlands.Cohomology`)

Here `Φ : C ⥤ D` is an additive functor between preadditive categories.

- `cocycleMap Φ z`: the cocycle obtained by applying `Φ` termwise to a cocycle
  `z : Cocycle K L n` (Mathlib's `Cochain.map`; it is a cocycle by `δ_map`);
  `cocycleMap_coe` records the underlying cochain.
- `map_equivHomShift_symm Φ z`: applying `Φ.mapHomologicalComplex` to the
  morphism `K ⟶ L⟦n⟧` of `z`, followed by the shift isomorphism of
  `Φ.mapHomologicalComplex` at `L`, gives the morphism of `cocycleMap Φ z`.
  Checked degreewise: all shift identifications are identities in each degree.

## The level derived map (namespace `Langlands.Cohomology`)

- `linearHomComplexHomologyToDerived R K L n`: for cochain complexes `K`, `L`
  in the abelian category `C`, the additive map from the degree `n` cohomology
  of `Hom^•(K, L)` to the morphisms `Q.obj K ⟶ (Q.obj L)⟦n⟧` in the derived
  category of `C`. It is `linearHomComplexHomologyHomotopyAddEquiv` followed
  by `Qh`, conjugated by `quotientCompQhIso` and the shift isomorphism of `Q`,
  exactly as the published `homComplexLimitToDerived` is built.
- `linearHomComplexHomologyToDerived_homologyπ R K L n c`: on the class of a
  cycle `c` its value is `Q.map` of the morphism `K ⟶ L⟦n⟧` of
  `linearHomComplexCocycle R K L n c`, followed by
  `(Q.commShiftIso n).hom.app L`.

## Evaluation of derived morphisms of inverse systems (namespace `Langlands.Cohomology.DivisibleSystem`)

- `derivedEval_Q_map K L n m f`: for complexes `K`, `L` of inverse systems and
  a chain map `f : K ⟶ L⟦n⟧`, the published `derivedEval K L n m` sends
  `Q.map f ≫ (Q.commShiftIso n).hom.app L` to `Q.map` of the evaluation of `f`
  at level `m` composed with the shift isomorphism of the evaluation functor on
  complexes, followed by `(Q.commShiftIso n).hom.app (evalComplex L m)`.
  Proof: naturality of `mapDerivedCategoryFactors` at `f` and its
  compatibility with the shift by `n`.

## Finite-level compatibility (namespace `Langlands.Cohomology.DivisibleSystem`)

Here `T` and `W` are `ℓ`-divisible systems of cochain complexes in `C`.

- `homComplexLimitToDerived_apply R T W n x`: by definition,
  `homComplexLimitToDerived R T W n x` is
  `linearHomComplexHomologyToDerived R (towerComplex T) (towerComplex W) n`
  applied to the image of `x` under the inverse of the published isomorphism
  `towerHomComplexIsoLimit` between `Hom^•(towerComplex T, towerComplex W)`
  and `homComplexLimit R T W`.
- `derivedEval_homComplexLimitToDerived R T W n m x` (theorem): for a class
  `x` in the degree `n` cohomology of `homComplexLimit R T W`,
  `derivedEval (towerComplex T) (towerComplex W) n m` of
  `homComplexLimitToDerived R T W n x` equals
  `linearHomComplexHomologyToDerived R (T m) (W m) n` of the image of `x`
  under the map on cohomology induced by the projection
  `limit.π (homComplexSystem R T W) (op m)`. In words: evaluating at level `m`
  the derived morphism attached to `x` gives the derived morphism attached to
  the level `m` component of `x`. Proof: transport `x` to the cohomology of
  `Hom^•(towerComplex T, towerComplex W)`, whose projection to level `m` is
  `towerHomComplexEval` (`towerHomComplexIsoLimit_hom_π`); write the class as
  the class of a cycle `c` (`homologyπ` is surjective); compute both sides
  with `linearHomComplexHomologyToDerived_homologyπ`, `derivedEval_Q_map` and
  `map_equivHomShift_symm`; finally, the cocycle of `c` mapped by evaluation at
  `m` is the cocycle of the image of `c` under `towerHomComplexEval`, since both
  have components `(z.v p q).app (op m)` (`towerCochainEval_v`).
- `homComplexLimitToCompatible R T W n`: the additive map
  `homComplexLimitToDerived R T W n` followed by the published
  `derivedToCompatible`, with values in the compatible families
  `compatibleDerived (towerComplex T) (towerComplex W) n`.
- `homComplexLimitToCompatible_apply_coe R T W n x m`: its level `m`
  component is `linearHomComplexHomologyToDerived R (T m) (W m) n` of the
  level `m` image of `x` (the theorem above).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), end of the proof of Proposition 4.10,
printed p.312 (one-based PDF page 14; Worker 61 read the rendered scanned
page). There Harris checks that the maps "(4.10.3)
`T_{m+1}(j, ẽ) → T_m(j, ẽ)`" are surjective and that "the complexes in (4.10.2)
satisfy a Mittag-Leffler condition", and concludes "the stronger (integral)
statement (4.10.4)
`E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n-1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒
H^{i+j}(S̄_{K(N)}, 𝓛̃)`".

The published `homComplexLimitToDerived` compares the cohomology of the
inverse limit of the Hom complexes at the finite levels `m` (the object built
from complexes of the shape of (4.10.2)) with morphisms in the derived category
of inverse systems (our interpretation of Harris's integral Ext groups; Harris
does not name the category). This module proves, in our own formulation, that
this comparison is compatible with the corresponding comparisons at each finite
level `m`. Harris's finite levels use the coefficients `𝒪/ℓ^m 𝒪`, which vary
with `m`; here all levels lie in the fixed category `C`.

The constructions, statements and proofs are ours; the module is derived.

## Scope

No map in this module is claimed to be injective, surjective or bijective, and
no Mittag-Leffler, `lim¹` or convergence result is proved. Harris's complexes
(4.10.2), the groups `T_m(j, ẽ)` and the change of coefficients `𝒪/ℓ^m 𝒪` are
not constructed. The comparison with the abutment `adicHyperextComparison`
(the case of `W` placed in degree `0`) is not restated levelwise here; it is
`homComplexLimitToDerived` followed by a fixed isomorphism. The existence of
derived categories for `C` and `ℕᵒᵖ ⥤ C` is assumed, not proved.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
