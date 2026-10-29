# Degree zero cohomology of the complex of compatible families

Author: Worker 61. Built on
`Langlands.Cohomology.DivisibleSystem.CompatibleCocycle`
(`compatibleCocycles`, `mem_compatibleCocycles_iff`,
`towerHomEquivCompatibleCocycles`), on
`Langlands.Cohomology.DivisibleSystem.CompatibleHomComplex`
(`compatibleCochains`, `compatibleδ`, `compatibleHomComplex`,
`compatibleHomComplexIsoLimit`), on
`Langlands.Cohomology.DivisibleSystem.HomSystem` (`cochainTransition`,
`cochainTransition_eq_iff`, `homComplexLimit`) and on
`Langlands.Cohomology.DivisibleSystem` (`DivisibleSystem`,
`DivisibleSystem.projection`, `DivisibleSystem.tower`,
`SmoothRepComplexDivisibleSystem`). From Mathlib it uses the Hom-complex API
`CochainComplex.HomComplex` (`Cochain.ofHom`, `Cochain.ofHomotopy`,
`Cochain.equivHomotopy`, `δ_ofHomotopy`, `δ_δ`), Mathlib's `Homotopy`, the
homology of a complex in terms of the short complex in degrees `-1, 0, 1`
(`HomologicalComplex.homologyIsoSc'`, `cyclesIsoSc'`,
`π_homologyIsoSc'_hom`, `cyclesIsoSc'_hom_iCycles`), the kernel-modulo-image
description of the homology of a short complex of modules
(`ShortComplex.moduleCatHomologyIso`, `moduleCatCyclesIso`,
`π_moduleCatCyclesIso_hom`, `moduleCatCyclesIso_hom_i`), and
`Submodule.Quotient.equiv`, `Submodule.map_comap_eq_of_surjective`.

Everything is in the namespace `Langlands.Cohomology.DivisibleSystem`, except
`smoothTowerHomQuotientEquivLimitHomologyZero`, which is in
`Langlands.Cohomology`.

`R` is a ring, `C` an `R`-linear abelian category with Hom-universe `v`, and
`T`, `W` are `ℓ`-divisible systems in `CochainComplex C ℤ`, with levels
`T m = T.obj m`, projections `T.projection h : T m ⟶ T m'` for `h : m' ≤ m`,
and inverse systems `T.tower`, `W.tower : ℕᵒᵖ ⥤ CochainComplex C ℤ`.
Recall: a cochain of degree `n` from `T m` to `W m` (Mathlib's `Cochain`) is
a family of morphisms `T m ^ p ⟶ W m ^ q` for `p + n = q`, with differential
`δ n n'`. A homotopy `H : Homotopy φ₁ φ₂` of chain maps has components
`H.hom p q : T m ^ p ⟶ W m ^ q`, zero unless `q + 1 = p`;
`Cochain.ofHomotopy H` is the `(-1)`-cochain with these components, and
Mathlib's `Cochain.equivHomotopy φ₁ φ₂` identifies homotopies `φ₁ ≃ φ₂` with
`(-1)`-cochains `z` such that `Cochain.ofHom φ₁ = δ (-1) 0 z +
Cochain.ofHom φ₂`. `cochainTransition T W h` is the transition of graded
morphisms from level `m` to level `m'`, `compatibleCochains R T W n` the
`R`-module of families `z m` of degree-`n` cochains fixed by the
transitions, `compatibleHomComplex R T W` the complex they form with the
levelwise differential `compatibleδ`, and `compatibleHomComplexIsoLimit R T W`
its comparison isomorphism with the limit `homComplexLimit R T W` of the Hom
complexes. The published CompatibleCocycle module gives the degree `0`
cocycles `compatibleCocycles R T W` (the kernel of `compatibleδ R T W 0 1`)
and the `R`-linear equivalence `towerHomEquivCompatibleCocycles R T W` from
`T.tower ⟶ W.tower`, sending `α` to the family
`m ↦ Cochain.ofHom (α.app (op m))`.

This module proves that the degree `0` cohomology of
`compatibleHomComplex R T W`, and of `homComplexLimit R T W`, is
`R`-linearly equivalent to the quotient of `T.tower ⟶ W.tower` by the
morphisms admitting a compatible null-homotopy.

## Compatible null-homotopies

- `projection_comp_homotopy_hom_iff T W h H H'`: for `m' ≤ m`, homotopies
  `H` at level `m` and `H'` at level `m'` (between any chain maps), the
  components commute with the projections,
  `(T.projection h).f p ≫ H'.hom p q = H.hom p q ≫ (W.projection h).f q` for
  all `p q`, if and only if `cochainTransition T W h (Cochain.ofHomotopy H) =
  Cochain.ofHomotopy H'`. Proof: by `cochainTransition_eq_iff` the right side
  is the same equation for the components `p → q` with `p + (-1) = q`; for
  the other pairs both sides of the left equation are zero because the
  homotopy components vanish there.
- `CompatibleNullHomotopy T W α`, for `α : T.tower ⟶ W.tower`: a structure
  consisting of a null-homotopy `homotopy m : Homotopy (α.app (op m)) 0` at
  every level `m` and the condition `comm`:
  `(T.projection h).f p ≫ (homotopy m').hom p q =
  (homotopy m).hom p q ≫ (W.projection h).f q` for all `m' ≤ m` and `p, q`.
- `CompatibleNullHomotopy.cochainTransition_ofHomotopy`: the `(-1)`-cochains
  `Cochain.ofHomotopy (H.homotopy m)` are fixed by the transitions (from
  `comm` by `projection_comp_homotopy_hom_iff`).
- `CompatibleNullHomotopy.δ_ofHomotopy`: `δ (-1) 0 (Cochain.ofHomotopy
  (H.homotopy m)) = Cochain.ofHom (α.app (op m))`, Mathlib's `δ_ofHomotopy`
  with the second chain map zero.
- `CompatibleNullHomotopy.ofCochains z hz hδ`: conversely, a family `z m` of
  `(-1)`-cochains fixed by the transitions (`hz`) with
  `δ (-1) 0 (z m) = Cochain.ofHom (α.app (op m))` (`hδ`) gives a compatible
  null-homotopy: the homotopy at level `m` is the one corresponding to
  `z m` under `Cochain.equivHomotopy`, and `comm` follows from `hz` by
  `projection_comp_homotopy_hom_iff`. `ofHomotopy_ofCochains` states that its
  `(-1)`-cochains are the `z m`.

## Coboundaries

- `addCommGroupCompatibleCocycles`: the additive group structure of
  `compatibleCocycles R T W`, which is Mathlib's `Submodule.addCommGroup`. It
  is declared as an instance because instance search did not find it through
  the two nested submodules (a submodule of `compatibleCochains R T W 0`,
  itself a submodule of a product) when forming quotients.
- `compatibleδ_mem_compatibleCocycles`: the differential
  `compatibleδ R T W (-1) 0 y` of a compatible family of `(-1)`-cochains is a
  degree `0` cocycle, levelwise by `δ_δ`.
- `compatibleCoboundaries R T W`: the `R`-submodule of
  `compatibleCocycles R T W` that is the range of `compatibleδ R T W (-1) 0`
  (with codomain restricted to the cocycles), i.e. the degree `0`
  coboundaries of `compatibleHomComplex R T W`.
  `mem_compatibleCoboundaries_iff`: a cocycle `z` is a coboundary if and only
  if there is a compatible family `y` of `(-1)`-cochains with
  `δ (-1) 0 (y m) = z m` for every `m`.
- `nullHomotopicTowerHoms R T W`: the `R`-submodule of `T.tower ⟶ W.tower`
  that is the preimage of `compatibleCoboundaries R T W` under
  `towerHomEquivCompatibleCocycles R T W`.
  `mem_nullHomotopicTowerHoms_iff_exists_cochains`: `α` lies in it if and only
  if there is a compatible family `y` of `(-1)`-cochains with
  `δ (-1) 0 (y m) = Cochain.ofHom (α.app (op m))` for every `m`.
- `mem_nullHomotopicTowerHoms_iff`: `α ∈ nullHomotopicTowerHoms R T W` if and
  only if `Nonempty (CompatibleNullHomotopy T W α)`. Proof: from such a
  family `y`, `CompatibleNullHomotopy.ofCochains`; from a compatible
  null-homotopy, its family of `(-1)`-cochains, by
  `cochainTransition_ofHomotopy` and `δ_ofHomotopy`.

## Degree zero cohomology

- `compatibleHomologyZeroEquiv R T W`:
  `(compatibleHomComplex R T W).homology 0 ≃ₗ[R]
  compatibleCocycles R T W ⧸ compatibleCoboundaries R T W`. It is the linear
  equivalence underlying the composite of the isomorphisms
  `homologyIsoSc' (-1) 0 1` (homology in degree `0` is the homology of the
  short complex `sc' (-1) 0 1` in degrees `-1, 0, 1`) and
  `moduleCatHomologyIso` of that short complex (Mathlib's chosen
  kernel-modulo-image description, whose kernel and image are
  `compatibleCocycles` and `compatibleCoboundaries` by definition).
- `iCycles_mem_compatibleCocycles`: the image in the degree `0` cochains of a
  degree `0` cycle (Mathlib's `cycles 0` object) lies in
  `compatibleCocycles R T W`.
- `compatibleHomologyZeroEquiv_homologyπ`: `compatibleHomologyZeroEquiv`
  sends the cohomology class `homologyπ 0 x` of a cycle `x` to the class of
  its image in the degree `0` cochains. Proof: by `π_homologyIsoSc'_hom`,
  `π_moduleCatCyclesIso_hom`, `moduleCatCyclesIso_hom_i` and
  `cyclesIsoSc'_hom_iCycles` applied to `x`.
- `towerHomHomologyClass R T W : (T.tower ⟶ W.tower) →ₗ[R]
  (compatibleHomComplex R T W).homology 0`: the class of the cocycle of `α`,
  i.e. the composite of `towerHomEquivCompatibleCocycles`, the quotient map
  and the inverse of `compatibleHomologyZeroEquiv`.
  `compatibleHomologyZeroEquiv_towerHomHomologyClass` states that
  `compatibleHomologyZeroEquiv` sends it to the class of
  `towerHomEquivCompatibleCocycles R T W α`.
- `towerHomHomologyClass_eq_homologyπ R T W α x hx`: if the image of the
  degree `0` cycle `x` in the cochains has level-`m` member
  `Cochain.ofHom (α.app (op m))` for every `m`, then
  `towerHomHomologyClass R T W α = homologyπ 0 x` (both have the same image
  under the equivalence `compatibleHomologyZeroEquiv`, by the previous
  lemmas).
- `towerHomHomologyClass_surjective`: every degree `0` class is the class of
  a morphism of inverse systems (composite of surjections).
- `ker_towerHomHomologyClass`: the kernel of `towerHomHomologyClass R T W` is
  `nullHomotopicTowerHoms R T W`.
- `towerHomHomologyClass_eq_zero_iff`: `towerHomHomologyClass R T W α = 0` if
  and only if `Nonempty (CompatibleNullHomotopy T W α)` (from the previous
  lemma and `mem_nullHomotopicTowerHoms_iff`).
- `towerHomQuotientEquivHomologyZero R T W`:
  `((T.tower ⟶ W.tower) ⧸ nullHomotopicTowerHoms R T W) ≃ₗ[R]
  (compatibleHomComplex R T W).homology 0`, the equivalence of quotients
  induced by `towerHomEquivCompatibleCocycles` (`Submodule.Quotient.equiv`;
  the image of `nullHomotopicTowerHoms` is `compatibleCoboundaries` by
  `Submodule.map_comap_eq_of_surjective`) followed by the inverse of
  `compatibleHomologyZeroEquiv`. The `simp` lemma
  `towerHomQuotientEquivHomologyZero_mk` states that the class of `α` goes
  to `towerHomHomologyClass R T W α` (by definition).

So the degree `0` cohomology of `compatibleHomComplex R T W` is the
`R`-module of morphisms of inverse systems `T.tower ⟶ W.tower` modulo those
admitting a compatible null-homotopy, i.e. of compatible homotopy classes
of such morphisms.

## The inverse limit of the Hom complexes

- `towerHomQuotientEquivLimitHomologyZero R T W`:
  `((T.tower ⟶ W.tower) ⧸ nullHomotopicTowerHoms R T W) ≃ₗ[R]
  (homComplexLimit R T W).homology 0`, the composite of
  `towerHomQuotientEquivHomologyZero R T W` with the image of
  `compatibleHomComplexIsoLimit R T W` under the degree `0` homology functor.
  So the identification is through the comparison isomorphism of
  CompatibleHomComplex with Mathlib's chosen limit object.
- `towerHomQuotientEquivLimitHomologyZero_mk`: the class of `α` goes to the
  image of `towerHomHomologyClass R T W α` under
  `homologyMap (compatibleHomComplexIsoLimit R T W).hom 0` (by definition).

## Smooth representations

`R : Type u` is a commutative ring, `G : Type v` a topological group, and
`T`, `W` are `ℓ`-divisible systems of `ℤ`-graded cochain complexes of smooth
representations (`SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ`).

- `smoothTowerHomQuotientEquivLimitHomologyZero R G T W`: the abbreviation
  for `DivisibleSystem.towerHomQuotientEquivLimitHomologyZero R T W`. Here a
  morphism of inverse systems is a family of `G`-equivariant chain maps
  `T m ⟶ W m` commuting with the projections, a compatible null-homotopy
  consists of `G`-equivariant homotopy components, and `homComplexLimit R T W`
  is the limit of the Hom complexes of graded `G`-equivariant `R`-linear
  maps.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed
pp.311-312 (one-based PDF pages 13-14). The passages are quoted in
`Langlands/Cohomology/DivisibleSystem/HomSystem.md`: Harris checks a
Mittag-Leffler condition for the complexes (4.10.2) as `m` varies, along the
maps (4.10.3) `T_{m+1}(j, ẽ) → T_m(j, ẽ)`, and passes to the inverse limit
over `m`. The published HomSystem module reads (4.10.3) as `homTransition`
and forms the inverse system of Hom complexes, CompatibleHomComplex
describes its limit by compatible families, and CompatibleCocycle identifies
its degree `0` cocycles with morphisms of inverse systems.

Harris does not state the identification of this module in the cited
passages. That the degree `0` cohomology of a Hom complex is the module of
homotopy classes of chain maps is standard (Mathlib's
`Cochain.equivHomotopy`); here it is combined with the levelwise description
of the limit, so that homotopies are replaced by compatible families of
homotopies. The formulation and proofs are ours.

## Scope

The module treats only degree `0`: it does not describe the cohomology of
`compatibleHomComplex` or `homComplexLimit` in nonzero degrees, Ext groups,
morphisms in homotopy or derived categories of inverse systems, Hom complexes
of inverse limits of the systems, or compatibility with the inclusions of
the `ℓ`-divisible systems (the morphisms are morphisms of the inverse systems
`T.tower ⟶ W.tower`). It does not compare compatible null-homotopies with
null-homotopies of the limits, and it does not identify Harris's complexes
(4.10.2) or modules `T_m(j, ẽ)` with Hom complexes of `ℓ`-divisible systems.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
