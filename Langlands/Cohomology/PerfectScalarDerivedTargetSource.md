# Source naturality of the perfect-source scalar adjunction

Author: Worker 727.

Module `Langlands.Cohomology.PerfectScalarDerivedTargetSource`, namespace
`Langlands.Cohomology`. It adds naturality statements to the published
`PerfectScalarDerivedTarget`. The published module proves naturality of
`ModuleComplex.perfectScalarDerivedTargetHomEquiv` in the derived target. This
module proves naturality in the strictly perfect source and states both
naturalities for the inverse equivalence. Everything is proved in the file,
with no hypotheses beyond those in the signatures and no proof holes.

## Section `General`

Data: abelian categories `C`, `D` with derived categories (independent
universes), additive functors `F : C ⥤ D`, `G : D ⥤ C` with `G` preserving
finite limits and finite colimits, and an adjunction `adj : F ⊣ G`.

- `derivedComplexAdjunctionUnit_naturality adj ψ` (with `@[reassoc]`): for a
  chain map `ψ : K ⟶ K'` of cochain complexes in `C`,

  `Q.map ψ ≫ derivedComplexAdjunctionUnit adj K'`
  `= derivedComplexAdjunctionUnit adj K ≫ G.mapDerivedCategory.map (Q.map (F.mapHomologicalComplex ψ))`.

  Here `derivedComplexAdjunctionUnit` is the published derived unit
  `Q(K) ⟶ G(Q(F K))` from `PerfectScalarAdjunctionProof`, which is `Q` applied
  to the unit of the termwise adjunction `complexAdjunction adj`, followed by
  `G.mapDerivedCategoryFactors.inv`. Proof: naturality of the termwise unit and
  of `G.mapDerivedCategoryFactors.inv`.

## Namespace `ModuleComplex`

Data: commutative rings `R`, `S` in one universe `u`, a ring map `φ : R →+* S`,
and derived categories of `R`- and `S`-modules (independent universes).
`baseChange φ` is the Library's termwise scalar extension of cochain complexes,
and `Res_φ` is `(ModuleCat.restrictScalars φ).mapDerivedCategory`.

- `perfectScalarDerivedTargetHomEquiv_naturality_source φ hK hK' ψ f`: for
  strictly perfect `K`, `K'`, a chain map `ψ : K ⟶ K'` and
  `f : Q(baseChange φ K') ⟶ Y`,

  `perfectScalarDerivedTargetHomEquiv φ K hK Y (Q.map (baseChange φ ψ) ≫ f)`
  `= Q.map ψ ≫ perfectScalarDerivedTargetHomEquiv φ K' hK' Y f`.

  Proof: the published forward formula (derived unit followed by `Res_φ`) and
  the naturality lemma above for `ModuleCat.extendRestrictScalarsAdj φ`.
- `perfectScalarDerivedTargetHomEquiv_symm_naturality_source φ hK hK' ψ b`: the
  same for the inverse. For `b : Q(K') ⟶ Res_φ Y`,
  `Q.map (baseChange φ ψ) ≫ (equiv K').symm b = (equiv K).symm (Q.map ψ ≫ b)`.
- `perfectScalarDerivedTargetHomEquiv_symm_naturality φ K hK b g`: the
  published target naturality, for the inverse. For
  `b : Q(K) ⟶ Res_φ Y` and `g : Y ⟶ Z`,
  `(equiv K).symm (b ≫ Res_φ.map g) = (equiv K).symm b ≫ g`.

## Provenance

Internal: formal naturality properties of the Library's own derived unit and
perfect-source scalar adjunction. Worker 950 requested the source-naturality
form for the perfect-model base-change construction in
`Langlands.AlgebraicGeometry.Modules.PerfectModelRestriction`. No literature
statement is formalized, and no external mathematical assertion is used.
