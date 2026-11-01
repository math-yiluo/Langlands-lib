# Scalar extension and cohomology of complexes of modules

Authors: Worker 727 and Worker 487. Worker 487 requested a cohomology-level
interface for perfect models (task ce5bb036). This module is its algebraic half.
The geometric half is
`Langlands.AlgebraicGeometry.Modules.PerfectModelHomology`.

Module `Langlands.Cohomology.ModuleComplex.BaseChangeHomology`, namespace
`Langlands.Cohomology.ModuleComplex`. Take a ring map `φ : R →+* S` of
commutative rings in one universe `u`, a cochain complex `K` of `R`-modules
indexed by `ℤ`, and an integer `n`. Write `S ⊗_R K` for the Library's termwise
scalar extension `(baseChange φ).obj K`. The module constructs the canonical
`S`-linear comparison

`c_n : S ⊗_R Hⁿ(K) ⟶ Hⁿ(S ⊗_R K)`

and proves:

- `c_n` is an isomorphism when `K` vanishes in degree `n + 1`;
- `c_n` is natural in chain maps;
- `c_n` is compatible with the Library's perfect-source scalar adjunction.

Everything is proved in the file. There are no hypotheses beyond those in the
signatures and no proof holes.

## Conventions

Write `φ^*` for Mathlib's `ModuleCat.extendScalars φ` and `φ_*` for
`ModuleCat.restrictScalars φ`. `adj` is Mathlib's
`ModuleCat.extendRestrictScalarsAdj φ : φ^* ⊣ φ_*`, and `adj.homEquiv` is its
Hom bijection `(φ^* A ⟶ B) ≃ (A ⟶ φ_* B)`. For complexes, `complexAdjunction
adj (.up ℤ)` is the Library's termwise adjunction `φ^* ⊣ φ_*` on cochain
complexes. `Hⁿ` of a complex is `HomologicalComplex.homology`. `Hⁿ` on the
derived category is `DerivedCategory.homologyFunctor _ n`, and `Q` is
`DerivedCategory.Q`. The derived-category declarations assume
`HasDerivedCategory` instances for `ModuleCat R` and `ModuleCat S` in arbitrary
universes `wC` and `wD`.

## Declarations

- `baseChangeHomologyMap φ K n` (a `def`): the comparison on homology of
  complexes, `φ^* (K.homology n) ⟶ (S ⊗_R K).homology n`. It is the
  `adj.homEquiv`-adjunct of `Hⁿ` of the unit `K ⟶ φ_* (S ⊗_R K)` of
  `complexAdjunction`, followed by Mathlib's `ShortComplex.mapHomologyIso` for
  the exact functor `φ_*`, which identifies `Hⁿ(φ_* -)` with `φ_* Hⁿ(-)`.
- `homEquiv_baseChangeHomologyMap`: the `adj.homEquiv`-adjunct of
  `baseChangeHomologyMap` is this defining `R`-linear map.
- `isIso_baseChangeHomologyMap_of_isZero φ K n h`: if `K.X (n + 1)` is zero,
  then `baseChangeHomologyMap φ K n` is an isomorphism. In the proof, the
  differentials `K.d n (n + 1)` and `(S ⊗_R K).d n (n + 1)` vanish. So the
  cycles in degree `n` are all of `K.X n`, respectively `φ^* (K.X n)`, by
  `HomologicalComplex.iCyclesIso`. This gives epimorphisms
  `pK : K.X n ⟶ K.homology n` and `pFK : φ^* (K.X n) ⟶ (S ⊗_R K).homology n`.
  The adjunction identities give `φ^* pK ≫ baseChangeHomologyMap = pFK`. This
  uses the Library's `DerivedPlus.homologyπ_mapHomologyIso_hom` and
  `HomologicalComplex.cyclesMap_i`. The homology of `S ⊗_R K` in degree `n` is a
  cokernel of the incoming differential (`homologyIsCokernel`). The map
  `φ^* pK` kills the image of `φ^* (K.d (n - 1) n)`, so it descends to an
  inverse `ψ`. Both inverse identities are checked after cancelling the
  epimorphisms `φ^* pK` (the image of an epimorphism under the left adjoint
  `φ^*`) and `homologyπ`.
- `baseChangeDerivedHomologyMap φ K n` (a `def`): the comparison
  `φ^* (Hⁿ(Q K)) ⟶ Hⁿ(Q (S ⊗_R K))` in the derived category. It is the
  `adj.homEquiv`-adjunct of `Hⁿ` of the Library's derived unit
  `derivedComplexAdjunctionUnit adj K : Q K ⟶ φ_* (Q (S ⊗_R K))`. This is
  followed by the component of the Library's
  `DerivedPlus.mapDerivedCategoryHomologyIso φ_* n`, which identifies
  `Hⁿ(φ_* -)` with `φ_* Hⁿ(-)` on derived categories.
- `homEquiv_baseChangeDerivedHomologyMap`: the adjunct of
  `baseChangeDerivedHomologyMap` is this defining `R`-linear map.
- `baseChangeDerivedHomologyMap_eq`: the derived comparison is
  `baseChangeHomologyMap` conjugated by Mathlib's
  `DerivedCategory.homologyFunctorFactors` isomorphisms
  `Hⁿ(Q -) ≅ (-).homology n`. The proof compares adjuncts. The Library's
  `DerivedPlus.mapDerivedCategoryHomologyIso_hom_app_Q_obj` expresses the
  homology isomorphism at a localized complex through
  `φ_*.mapDerivedCategoryFactors.hom`. Unfolding `derivedComplexAdjunctionUnit`
  produces `mapDerivedCategoryFactors.inv`, and the two cancel. The rest is
  naturality of `homologyFunctorFactors` at the complex-level unit.
- `isIso_baseChangeDerivedHomologyMap_of_isZero φ K n h`: if `K.X (n + 1)` is
  zero, then the derived comparison is an isomorphism. This follows from the
  previous two results.
- `baseChangeDerivedHomologyMap_naturality φ n ψ` (with a `@[reassoc]`
  variant): for a chain map `ψ : K ⟶ K'`,
  `φ^* (Hⁿ(Q ψ)) ≫ c_n(K') = c_n(K) ≫ Hⁿ(Q (S ⊗_R ψ))`. The proof compares
  adjuncts and uses the Library's `derivedComplexAdjunctionUnit_naturality` and
  `DerivedPlus.mapDerivedCategoryHomologyIso_hom_naturality`.
- `isIso_baseChangeDerivedHomologyMap_iff φ n ψ hψ hψ'`: if `Q ψ` and
  `Q (S ⊗_R ψ)` are isomorphisms, then `c_n(K)` is an isomorphism if and only if
  `c_n(K')` is. This follows from naturality: cancel the invertible outer
  factors with `IsIso.of_isIso_comp_left` and `IsIso.of_isIso_comp_right`.
- `homEquiv_baseChangeDerivedHomologyMap_comp φ K n hK b`: for a strictly
  perfect `K` (`hK : IsStrictlyPerfect K`) and a derived morphism
  `b : Q (S ⊗_R K) ⟶ Y`, the adjunct of `c_n ≫ Hⁿ(b)` is
  `Hⁿ(perfectScalarDerivedTargetHomEquiv φ K hK Y b)` followed by the component
  of `mapDerivedCategoryHomologyIso` at `Y`. Here
  `perfectScalarDerivedTargetHomEquiv` is the Library's perfect-source scalar
  adjunction. The proof rewrites it with its defining lemma
  `perfectScalarDerivedTargetHomEquiv_apply` as the derived unit followed by
  `φ_*` of `b`, and then uses naturality of `mapDerivedCategoryHomologyIso`.

## Provenance

This is internal infrastructure. It formalizes the canonical comparison
`S ⊗_R Hⁿ(K) ⟶ Hⁿ(S ⊗_R K)` and its standard properties: right exactness of
`S ⊗_R -` gives an isomorphism in the top degree of a cokernel presentation,
and the map is natural. No literature statement is formalized as such. Worker
487 requested the interface so that perfect models of cohomology can be compared
with the cohomology base-change maps (task ce5bb036).
