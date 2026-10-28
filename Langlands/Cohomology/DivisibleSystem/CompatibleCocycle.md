# Degree zero cocycles of the complex of compatible families

Author: Worker 61. Built on
`Langlands.Cohomology.DivisibleSystem.CompatibleHomComplex`
(`compatibleCochains`, `compatibleδ`, `compatibleHomComplex`,
`compatibleHomComplexIsoLimit`, `compatibleHomComplexIsoLimit_hom_π`), on
`Langlands.Cohomology.DivisibleSystem.HomSystem` (`homTransition`,
`homTransition_eq_iff`, `projection_comp_homTransition`, `homTransition_app`,
`cochainTransition`, `cochainTransition_eq_iff`, `homComplexSystem`,
`homComplexLimit`) and on `Langlands.Cohomology.DivisibleSystem`
(`DivisibleSystem`, `DivisibleSystem.degree`, `DivisibleSystem.tower`,
`SmoothRepComplexDivisibleSystem`). From Mathlib it uses the Hom-complex API
`CochainComplex.HomComplex`: `Cochain.ofHom`, `Cochain.ofHom_comp`,
`Cochain.ofHom_add`, `Cochain.ofHom_injective`, `Cochain.ext₀`, `δ_ofHom`,
and the cocycles `Cocycle.mk`, `Cocycle.homOf` with
`Cocycle.cochain_ofHom_homOf_eq_coe`; and `NatTrans.app_add`,
`NatTrans.app_smul`, `HomologicalComplex.congr_hom`.

Everything is in the namespace `Langlands.Cohomology.DivisibleSystem`, except
`cochain_ofHom_smul`, `kerDLinearEquivOfIso`, `kerDLinearEquivOfIso_apply_coe`
and `smoothTowerHomEquivLimitCocycles`, which are in `Langlands.Cohomology`.

`R` is a ring, `C` an `R`-linear abelian category with Hom-universe `v`, and
`T`, `W` are `ℓ`-divisible systems in `CochainComplex C ℤ`, with levels
`T m = T.obj m` and inverse systems `T.tower`, `W.tower : ℕᵒᵖ ⥤
CochainComplex C ℤ` (the levels with the projections). Recall: a cochain of
degree `n` from `T m` to `W m` (Mathlib's `Cochain`) is a family of morphisms
`T m ^ p ⟶ W m ^ q` for `p + n = q`, with differential `δ n n'`; a
`0`-cochain is a cocycle (`δ 0 1 z = 0`) exactly when it comes from a chain
map, by Mathlib's `Cochain.ofHom` and `Cocycle.homOf`. For `m' ≤ m` and
`h : m' ≤ m`, `homTransition T W h f : T m' ⟶ W m'` is the morphism with
`T.projection h ≫ homTransition T W h f = f ≫ W.projection h` (Harris's map
(4.10.3) in the published HomSystem module), and `cochainTransition T W h`
is its degreewise analogue on cochains. `compatibleCochains R T W n` is the
`R`-module of families `z m` of degree-`n` cochains fixed by the transitions,
`compatibleHomComplex R T W` the complex they form with the levelwise
differential `compatibleδ`, and `compatibleHomComplexIsoLimit R T W` its
comparison isomorphism with the limit `homComplexLimit R T W` of the inverse
system `homComplexSystem R T W` of Hom complexes.

This module proves that the morphisms of inverse systems
`T.tower ⟶ W.tower` correspond, by an explicit `R`-linear equivalence, to
the degree `0` cocycles of `compatibleHomComplex R T W` and of
`homComplexLimit R T W`.

## Auxiliary lemmas

- `cochain_ofHom_smul r f`: for an `R`-linear preadditive category,
  `Cochain.ofHom (r • f) = r • Cochain.ofHom f` for a chain map `f`; both
  sides have component `r • f.f p` in every degree `p` (`Cochain.ext₀`).
- `kerDLinearEquivOfIso e i j`: for an isomorphism `e : K ≅ L` of complexes
  in `CochainComplex (ModuleCat.{v} R) ℤ`, the `R`-linear equivalence between
  the kernels of `K.d i j` and `L.d i j` given by the components
  `e.hom.f i` and `e.inv.f i`. They map kernel to kernel because `e.hom` and
  `e.inv` commute with the differentials, and they are mutually inverse by
  `e.hom_inv_id` and `e.inv_hom_id` in degree `i`.
  `kerDLinearEquivOfIso_apply_coe` states that the underlying element of the
  image of `x` is `(e.hom.f i) x` (by definition).
- `homTransition_f T W h f p`: for `ℓ`-divisible systems of cochain
  complexes and a chain map `f : T m ⟶ W m`, the degree-`p` component of
  `homTransition T W h f` is `homTransition (T.degree p) (W.degree p) h
  (f.f p)`, the transition of the degree-`p` systems. Proof: by
  `homTransition_eq_iff` for the degree-`p` systems, it suffices that the
  degree-`p` component of `projection_comp_homTransition` holds.
- `cochainTransition_ofHom T W h f`: `cochainTransition T W h
  (Cochain.ofHom f) = Cochain.ofHom (homTransition T W h f)`. Proof: by
  `cochainTransition_eq_iff` and `Cochain.ofHom_comp` both sides reduce to
  `projection_comp_homTransition`.

## Compatible cocycles

- `compatibleCocycles R T W`: the `R`-submodule of
  `compatibleCochains R T W 0` that is the kernel of `compatibleδ R T W 0 1`.
  `compatibleCocycles_eq_ker_d` states that it is the kernel of the
  differential `(compatibleHomComplex R T W).d 0 1` (by definition), i.e.
  these are the degree `0` cocycles of `compatibleHomComplex R T W`.
- `mem_compatibleCocycles_iff`: a compatible family `z` of `0`-cochains lies
  in `compatibleCocycles R T W` if and only if `δ 0 1 (z m) = 0` for every
  `m`, because `compatibleδ` is applied levelwise.
- `compatibleCocycleAt R T W z m`: the member at level `m` of
  `z : compatibleCocycles R T W`, as a Mathlib `Cocycle (T m) (W m) 0`.
- `compatibleCocycleHom R T W z m : T m ⟶ W m`: the chain map
  `Cocycle.homOf (compatibleCocycleAt R T W z m)`.
  `compatibleCocycleHom_f` states that its degree-`p` component is the
  component `(z m).v p p _` of the cochain (by definition), and
  `ofHom_compatibleCocycleHom` that `Cochain.ofHom` of it is `z m`.
- `homTransition_compatibleCocycleHom R T W z h`: for `m' ≤ m`,
  `homTransition T W h (compatibleCocycleHom R T W z m) =
  compatibleCocycleHom R T W z m'`. Proof: `Cochain.ofHom` is injective, and
  after `cochainTransition_ofHom` and `ofHom_compatibleCocycleHom` this is
  the compatibility `cochainTransition T W h (z m) = z m'` of `z`.

## Morphisms of inverse systems

- `towerHomOfCompatibleCocycle R T W z : T.tower ⟶ W.tower`: the natural
  transformation with component `compatibleCocycleHom R T W z m` at `m`.
  Naturality for `m' ≤ m` is `T.projection h ≫ (component at m') =
  (component at m) ≫ W.projection h`, which is
  `homTransition_compatibleCocycleHom` read through `homTransition_eq_iff`.
  Its `simps` lemma `towerHomOfCompatibleCocycle_app` gives the components.
- `compatibleCocycleOfTowerHom R T W α`: for `α : T.tower ⟶ W.tower`, the
  family `m ↦ Cochain.ofHom (α.app (op m))`. It is compatible by
  `cochainTransition_ofHom` and `homTransition_app` (a morphism of inverse
  systems is fixed by the transitions), and each member is a cocycle by
  `δ_ofHom`. `compatibleCocycleOfTowerHom_coe` states the level-`m` member
  (by definition).
- `towerHomEquivCompatibleCocycles R T W`:
  `(T.tower ⟶ W.tower) ≃ₗ[R] compatibleCocycles R T W`, with forward map
  `compatibleCocycleOfTowerHom` and inverse `towerHomOfCompatibleCocycle`.
  Additivity and `R`-linearity hold levelwise by `NatTrans.app_add`,
  `Cochain.ofHom_add`, `NatTrans.app_smul` and `cochain_ofHom_smul`. Both
  composites are identities levelwise by `ofHom_compatibleCocycleHom`; for
  the composite on `T.tower ⟶ W.tower` this is combined with the
  injectivity of `Cochain.ofHom` on chain maps. The
  `simp` lemmas `towerHomEquivCompatibleCocycles_apply_coe` and
  `towerHomEquivCompatibleCocycles_symm_apply_app` state the level-`m` member
  `Cochain.ofHom (α.app (op m))` of the image of `α` and the component
  `compatibleCocycleHom R T W z m` of the preimage of `z`.

The morphisms here are morphisms of the inverse systems
`T.tower ⟶ W.tower`; compatibility with the inclusions of the
`ℓ`-divisible systems is not required.

## The inverse limit of the Hom complexes

- `towerHomEquivLimitCocycles R T W`:
  `(T.tower ⟶ W.tower) ≃ₗ[R] ker ((homComplexLimit R T W).d 0 1)`, the
  composite of `towerHomEquivCompatibleCocycles R T W` with
  `kerDLinearEquivOfIso (compatibleHomComplexIsoLimit R T W) 0 1`. So the
  degree `0` cocycles of the limit of the Hom complexes (Mathlib's chosen
  limit object) are the morphisms of inverse systems; the identification is
  through the comparison isomorphism of CompatibleHomComplex.
- `limit_π_f_towerHomEquivLimitCocycles R T W α m`: the degree-`0`
  component of the limit projection `limit.π (homComplexSystem R T W) (op m)`
  sends the cocycle of `α` to `Cochain.ofHom (α.app (op m))`; this is
  `compatibleHomComplexIsoLimit_hom_π` in degree `0`.
- `limit_π_f_eq_ofHom_towerHomEquivLimitCocycles_symm_app R T W x m`: for a
  degree `0` cocycle `x` of `homComplexLimit R T W`, its projection to level
  `m` is `Cochain.ofHom` of the component at `m` of the corresponding
  morphism of inverse systems; this is the previous lemma applied to the
  preimage of `x`.

## Smooth representations

`R : Type u` is a commutative ring, `G : Type v` a topological group, and
`T`, `W` are `ℓ`-divisible systems of `ℤ`-graded cochain complexes of smooth
representations (`SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ`).

- `smoothTowerHomEquivLimitCocycles R G T W`: the abbreviation for
  `DivisibleSystem.towerHomEquivLimitCocycles R T W`,
  `(T.tower ⟶ W.tower) ≃ₗ[R] ker ((homComplexLimit R T W).d 0 1)`. Here a
  morphism of inverse systems is a family of `G`-equivariant chain maps
  `T m ⟶ W m` commuting with the projections, and `homComplexLimit R T W`
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
and forms the inverse system of Hom complexes; CompatibleHomComplex
describes its limit by compatible families.

Harris does not state the identification of this module in the cited
passages. That the degree `0` cocycles of the limit are the compatible
families of chain maps, i.e. the morphisms of the inverse systems, is the
standard fact that `0`-cocycles of a Hom complex are chain maps, combined
with the levelwise description of the limit; the formulation and proofs are
ours, from Mathlib's `Cocycle.homOf` and `Cochain.ofHom`.

## Scope

The module does not treat homotopies, coboundaries or the cohomology of
`compatibleHomComplex` or `homComplexLimit` (so no `H^0` or morphisms in the
homotopy or derived category), Ext groups, cocycles of nonzero degree, Hom
complexes of inverse limits of the systems, or compatibility with the
inclusions of the `ℓ`-divisible systems. It does not identify Harris's
complexes (4.10.2) or modules `T_m(j, ẽ)` with Hom complexes of
`ℓ`-divisible systems.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
