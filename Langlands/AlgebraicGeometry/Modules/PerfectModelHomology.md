# Perfect models and cohomology base change maps

Authors: Worker 727 and Worker 487. Worker 487 requested this cohomology-level
interface for perfect models (task ce5bb036). Degree zero is the case they
need.

Module `Langlands.AlgebraicGeometry.Modules.PerfectModelHomology`, namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. It relates the Library's
base-changed perfect model `perfectModelBaseChange` to the Library's `T`-linear
cohomology base-change maps `scalarBaseChangeMap` (all degrees) and
`scalarSectionsBaseChangeMap` (relative sections). As a consequence, those maps
are isomorphisms exactly when the algebraic comparison
`T ⊗_R Hⁿ(K) ⟶ Hⁿ(T ⊗_R K)` is. The algebraic comparison comes from
`Langlands.Cohomology.ModuleComplex.BaseChangeHomology`.

Everything is proved in the file. There are no hypotheses beyond those in the
signatures and no proof holes.

## Setting and conventions

All schemes and rings are in one universe `u`. Every declaration takes the
following data:

- a ring map `φ : R ⟶ T` of commutative rings;
- morphisms `f : X ⟶ Spec R`, `f' : X' ⟶ Spec T` and `p : X' ⟶ X`, with a
  pullback square `hp : IsPullback p f' f (Spec.map φ)`;
- a line bundle `L : LineBundle X` (the Library's `Picard.LineBundle`);
- a cochain complex `K` of `R`-modules indexed by `ℤ`, with
  `hK : ModuleComplex.IsStrictlyPerfect K`;
- a derived morphism `a : Q K ⟶ RΓ_R(X, L)`.

Here `RΓ_R(X, L)` is the Library's
`(DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj L.obj`,
and `Q` is `DerivedCategory.Q`. The derived categories are the standard ones
(`HasDerivedCategory.standard`). Write:

- `T ⊗_R K` for `(ModuleComplex.baseChange φ.hom).obj K`, and `φ^*` for
  `ModuleCat.extendScalars φ.hom`;
- `p^* L` for `(Scheme.Modules.pullback p).obj L.obj`;
- `Hⁿ` for `DerivedCategory.homologyFunctor _ n`;
- `ιₙ` for the Library's `DerivedPlus.homologyIso (relativeGlobalSections f)
  (injectiveResolution L.obj) n : Hⁿ(RΓ_R(X, L)) ≅ (relativeGlobalSections f).rightDerived n L`,
  whose target is by definition `(relativeCohomology f n).obj L.obj`, and `ι'ₙ` for the same
  isomorphism for `f'` and `p^* L`;
- `ζ` and `ζ'` for the Library's `relativeCohomologyZeroIso f` and
  `relativeCohomologyZeroIso f'` (`H⁰ ≅ Γ`);
- `c_n` for `ModuleComplex.baseChangeDerivedHomologyMap φ.hom K n :
  φ^* Hⁿ(Q K) ⟶ Hⁿ(Q (T ⊗_R K))`;
- `b` for `perfectModelBaseChange hp L hK a : Q (T ⊗_R K) ⟶ RΓ_T(X', p^* L)`;
- `β_n` for `scalarBaseChangeMap φ f f' p hp.w L.obj h n`, where
  `h = isZero_higherDirectImage_pullback_lineBundle_of_isPullback hp L`
  discharges the vanishing hypothesis. Write `σ` for
  `scalarSectionsBaseChangeMap φ f f' p hp.w L.obj`.

The degree-zero statements write the index as `((0 : ℕ) : ℤ)`, the cast of the
natural number `0`, as in `Hⁿ` for `n : ℕ`.

## Declarations

- `perfectModelBaseChange_homology hp L hK a n`: for every `n : ℕ`,

  `c_n ≫ Hⁿ(b) ≫ ι'ₙ.hom = φ^* (Hⁿ(a) ≫ ιₙ.hom) ≫ β_n`.

  Both sides are compared through the scalar adjunction `adj.homEquiv`, where
  `adj` is `ModuleCat.extendRestrictScalarsAdj φ.hom`. On the left,
  `homEquiv_baseChangeDerivedHomologyMap_comp` turns the adjunct of `c_n ≫ Hⁿ(b)`
  into `Hⁿ` of `perfectScalarDerivedTargetHomEquiv φ.hom K hK _ b`. By the
  Library's `perfectScalarDerivedTargetHomEquiv_perfectModelBaseChange`, this is
  `a ≫ derivedBaseChangeMapLineBundle hp L`. On the right, the Library's
  `scalarBaseChangeMap_homEquiv` turns the adjunct of `β_n` into the published
  semilinear `baseChangeMap`. The remaining identity is the Library's
  `derivedBaseChangeMap_homology`: `Hⁿ` of the derived base change map is
  `baseChangeMap`, through the homology identifications.
- `perfectModelBaseChange_homology_zero hp L hK a`: in degree zero,

  `c_0 ≫ H⁰(b) ≫ ι'₀.hom ≫ ζ'.hom = φ^* (H⁰(a) ≫ ι₀.hom ≫ ζ.hom) ≫ σ`.

  It follows from the previous theorem at `n = 0` and the Library's
  `scalarBaseChangeMap_zero`, which writes `β_0` as
  `φ^* ζ.hom ≫ σ ≫ ζ'.inv`.
- `isIso_scalarBaseChangeMap_iff_of_perfectModel hp L hK a n ha hb`: if `a` and
  `b` are isomorphisms (`ha : IsIso a`, `hb : IsIso b`), then `β_n` is an
  isomorphism if and only if `c_n` is. Every other factor in
  `perfectModelBaseChange_homology` is an isomorphism, so this follows by
  cancelling them (`IsIso.of_isIso_comp_left`, `IsIso.of_isIso_comp_right`).
- `isIso_scalarBaseChangeMap_of_perfectModel_of_isZero hp L hK a n ha hb hK1`:
  if moreover `K.X ((n : ℤ) + 1)` is zero (`hK1`), then `β_n` is an
  isomorphism. This combines the previous theorem with
  `ModuleComplex.isIso_baseChangeDerivedHomologyMap_of_isZero`.
- `isIso_scalarSectionsBaseChangeMap_iff_of_perfectModel hp L hK a ha hb`: if `a`
  and `b` are isomorphisms, then `σ : φ^* Γ(X, L) ⟶ Γ(X', p^* L)` is an
  isomorphism if and only if `c_0` is. By `scalarBaseChangeMap_zero`, `β_0` and
  `σ` differ by the isomorphisms `φ^* ζ.hom` and `ζ'.inv`, so the result reduces
  to the previous criterion at `n = 0`.
- `isIso_scalarSectionsBaseChangeMap_of_perfectModel_of_isZero hp L hK a ha hb
  hK1`: if `a` and `b` are isomorphisms and `K.X 1` is zero, then `σ` is an
  isomorphism.

The hypotheses `ha` and `hb` are separate. The module does not claim that `b`
is an isomorphism whenever `a` is.

## Provenance

This is internal infrastructure. It formalizes the standard step in cohomology
and base change: if `RΓ(X, L)` is represented by a perfect complex `K`
compatibly with base change, then the base-change maps on cohomology are the
maps `T ⊗_R Hⁿ(K) ⟶ Hⁿ(T ⊗_R K)`. By right exactness of the tensor product,
the degree-`n` map is an isomorphism when `K` vanishes in degree `n + 1`. No literature statement is
formalized as such. The proof uses only the Library's `perfectModelBaseChange`,
`scalarBaseChangeMap`, `derivedBaseChangeMap_homology` and
`scalarBaseChangeMap_zero`, together with the companion module
`BaseChangeHomology`.
