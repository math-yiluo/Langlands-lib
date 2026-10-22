# ℓ-divisible systems of resolutions

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem` (ℓ-divisible systems, Harris 1999,
(2.1)), `Langlands.Cohomology.CokernelComplex` (iterated-cokernel complexes of
a coaugmented endofunctor) and `Langlands.Sheaf.Equivariant.Godement.Smooth`
(the smooth Godement complex) and
`Langlands.Cohomology.DivisibleSystem.Coaugmented` (the residual and term
systems of Harris's Lemma 2.2). All names below are in the namespace
`Langlands.Cohomology.DivisibleSystem`. Write `T m` for `T.obj m`.

Harris's Lemma 2.2 (1999, printed p.304) gives, for each `m`, a resolution
`0 → ℤ/ℓ^mℤ → F_m^0 → F_m^1 → ⋯` such that each `{F_m^q}` is an
`ℓ`-divisible system. On p.305 he truncates the complexes `F_m^•` and says
that the cohomology is "canonically calculated by an ℓ-divisible system of
finite-length complexes [...], in the obvious sense". The parent module fixes
that sense: an `ℓ`-divisible system in an abelian category of complexes, whose
conditions hold in each degree. This module shows that systems
`S 0, S 1, …` joined by morphisms of systems with vanishing consecutive
composites form such a system of complexes. It applies this to the term
systems of the Coaugmented module, so the resolutions of Lemma 2.2 form one
`ℓ`-divisible system of complexes.

## Systems of complexes from systems of terms

`C` is an abelian category and `ℓ : ℕ`. `S : ℕ → DivisibleSystem C ℓ` is a
sequence of `ℓ`-divisible systems, `d q : S q ⟶ S (q + 1)` are morphisms of
`ℓ`-divisible systems, and `sq q m` says that
`(d q).tower.app m ≫ (d (q + 1)).tower.app m = 0` for every level `m`.
Morphisms of `ℓ`-divisible systems have no zero morphisms in this
formalization, so the condition is stated at every level.

- `levelComplex S d sq m` is the cochain complex, indexed by `ℕ`, with terms
  the level-`m` objects of the systems `S q` and differentials the level-`m`
  components of `d q` (`CochainComplex.of`). `levelComplex_d` gives its
  differential from degree `q` to `q + 1`.
- `levelMap S d sq f` is the chain map between levels whose components are the
  tower maps (Harris's `j`) of the systems `S q`. `levelInclusion S d sq h`,
  for `m' < m`, is the chain map whose components are the inclusions (Harris's
  `i`). They are chain maps because the `d q` are morphisms of systems: they
  commute with the tower maps and with the inclusions.
- `complexTower S d sq : ℕᵒᵖ ⥤ CochainComplex C ℕ` is the functor with these
  objects and maps.
- `ofDegrees S d sq : DivisibleSystem (CochainComplex C ℕ) ℓ` has tower
  `complexTower` and inclusions `levelInclusion`. Each condition of an
  `ℓ`-divisible system holds in the category of complexes because it holds in
  each degree. The short exact rows (2.1) use Mathlib's
  `HomologicalComplex.shortExact_of_degreewise_shortExact`; `torsion_exact` and
  `flat` use `HomologicalComplex.exact_of_degreewise_exact`. The equations
  `powSMul_eq_zero` and `inclusion_comp` are checked degreewise.
- `ofDegrees_obj_X`, `ofDegrees_obj_d`, `ofDegrees_inclusion_f` and
  `ofDegrees_projection_f` give the degree-`q` term, the differential, the
  inclusions and the projections of `ofDegrees S d sq` at level `m`.
- `ofDegreesDegreeIso S d sq q : (ofDegrees S d sq).degree q ≅ S q` says that
  the degree-`q` system of `ofDegrees` (the parent module's `degree`) is
  `S q`. Its components are identities.

The module does not prove the converse, that every `ℓ`-divisible system of
complexes arises from its degree systems in this way.

## The resolutions of Lemma 2.2

`F : C ⥤ C` is additive and preserves finite limits and finite colimits,
`η : 𝟭 C ⟶ F` has monomorphic components, and `T : DivisibleSystem C ℓ`. These
are the hypotheses of the general section of the Coaugmented module; the
exactness of `F` stands for Harris's Fact 3 and is assumed, not proved.

- `resolutionSystem F η T` is `ofDegrees` applied to the term systems
  `T.termSystem F η q` (Harris's `{F_m^q}`) and the term differentials
  `T.termDifferential F η q`. Their consecutive composites vanish by the
  Coaugmented module's `termDifferential_comp_termDifferential_tower_app`.
- `resolutionSystemDegreeIso F η T q` identifies its degree-`q` system with
  `T.termSystem F η q`.
- `resolutionSystem_obj_d` gives the differential at level `m` as the
  level-`m` component of `T.termDifferential F η q`.
- `resolutionSystemObjIso F η T m` identifies level `m` with the published
  iterated-cokernel complex `CokernelComplex.complex F η (T m)`. Its components
  are the Coaugmented module's `termSystemObjIso`, and it commutes with the
  differentials by `termDifferential_comp_termSystemObjIso_hom`.
- `resolutionSystem_obj_exactAt F η T m q` says that level `m` is exact in
  degree `q + 1`. This is the Coaugmented module's `termDifferential_exact`.

Degree 0 is not covered by `resolutionSystem_obj_exactAt`: the resolved object
`T m` is not a term of these complexes. Exactness of `T m ⟶ F^0 m ⟶ F^1 m` is
the Coaugmented module's `residualInclusion_termDifferential_exact` at
`q = 0`, and the monomorphism `T m ⟶ F^0 m` is its instance for
`residualInclusion`. The module does not identify the degree-zero cohomology
of the level complexes with `T m`.

## The smooth Godement functor

`R`, `G` and `X` are as in the published `SmoothTopologicalSheaf R G X`: they
lie in one universe, `G` is a topological group acting on `X` by continuous
translations, and `HasStableNeighbourhoods G X` holds.
`T : SmoothSheafDivisibleSystem R G X ℓ`. The exactness of the degree-zero
smooth Godement functor is not proved in the Library. It is Worker 3's
proposition `SmoothGodementZeroExactStatement R G X`, and both declarations
below take a proof `h` of it as an explicit argument.

- `smoothGodementResolutionSystem h T` is `resolutionSystem` for
  `smoothZeroFunctor R G X` and `smoothCoaugmentation R G X`. It is an
  `ℓ`-divisible system of cochain complexes of smooth equivariant sheaves.
- `smoothGodementResolutionSystemObjIso h T m` identifies its level `m` with
  `smoothComplex R G X (T m)`, the published smooth Godement complex of `T m`.
  It is `resolutionSystemObjIso`; the published `smoothComplex` is by
  definition `CokernelComplex.complex` for this functor and coaugmentation.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.304–305. Worker 61
read the pages in the scanned original.

1. Systems of complexes. Lemma 2.2 states only that each `{F_m^q}` is an
   `ℓ`-divisible system. On p.305 Harris forms the truncations
   `G_m^• = τ_{≤D+1}(F_m^•)` and calls the resulting family "an ℓ-divisible
   system of finite-length complexes [...], in the obvious sense". This needs
   the differentials of `F_m^•` to commute with the maps `i` and `j`. In the
   induction of the Coaugmented module they are morphisms of systems, so they
   do. `resolutionSystem` records the family `{F_m^•}` as one system of
   complexes, in the sense fixed by item 7 of the Markdown of
   `Langlands.Cohomology.DivisibleSystem`.
2. Degrees. The complexes are indexed by `ℕ`, as are the resolutions of Lemma
   2.2. They contain the terms `F_m^q` only; the augmentation from `T m` is
   kept separately, as above.
3. Hypotheses and general `T`. As in the Coaugmented module, Fact 3 is a
   hypothesis, the construction takes any `ℓ`-divisible system `T`, and Lemma
   2.2 is the case of the constant sheaves `ℤ/ℓ^mℤ`, which are not constructed
   here.
4. Not proved. The `R Γ`-acyclicity of the `F_m^q`, the truncations and Lemma
   2.2 bis, and the free resolutions and the complexes `C_m^•` of pp.305–306
   are not formalized here.

`ofDegrees` is the "obvious sense" of a system of complexes for complexes given
degree by degree, and `resolutionSystem` is the system of the resolutions of
Lemma 2.2. The level complexes, maps and isomorphisms, the exactness lemma and
the degreewise identifications are derived. The smooth declarations are the
instance of the general construction for the functor Harris uses, with Fact 3
as a hypothesis.

## Scope

The module does not prove Harris's Facts 3 and 4 for any Godement functor, the
exactness of the smooth Godement functor, any acyclicity, or any statement
about the cohomology of the level complexes. It does not construct the
constant systems `ℤ/ℓ^mℤ` or the truncated systems of Lemma 2.2 bis.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
