# Reduction sequences for right derived functors of ℓ-divisible systems

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem` (Worker 61: `DivisibleSystem` with
`tower`, `obj`, `projection`, `inclusion`, `powSMul_eq_zero`,
`inclusion_comp`, `shortExact`, `torsion_exact`, `flat`, `epi_projection`,
`isZero_obj_zero` and the instance `mono_inclusion`; `powSMul`,
`comp_powSMul`, `powSMul_comp_powSMul`, `map_powSMul`),
`Langlands.Cohomology.DivisibleSystem.Colimit` (Worker 61:
`shortComplex_exact_of_evaluation`),
`Langlands.Cohomology.DivisibleSystem.ReductionSequence` (Worker 61:
`cokernelKernelShortComplex`, `cokernelKernelShortComplex_shortExact`),
`Langlands.Cohomology.RightDerivedSequence` (Worker 61: the connecting maps
`DerivedPlus.rightDerivedδ` of the long exact sequence of right derived
functors, `rightDerived_map_comp_map`, `rightDerived_map_comp_δ`,
`rightDerivedδ_comp_map`, `rightDerived_exact₁`, `rightDerived_exact₂`,
`rightDerived_exact₃`, `rightDerivedδ_naturality`) and
`Langlands.Cohomology.DivisibleSystem.EtaleAdicCohomology` (Worker 61:
`EtaleAdicCohomology.adicCohomology`,
`EtaleAdicCohomology.harrisEtaleAdicCohomology`). Through their imports it
uses `reductionπ` (`Langlands.Cohomology.DivisibleSystem.Reduction`), Worker
13's `EtaleDerivedSections.ModuleSheaf`, `EtaleDerivedSections.sections` and
`EtaleDerivedSections.cohomology` (`Langlands.Geometry.EtaleDerivedSections`),
the published `harrisEtaleDivisibleSystem`
(`Langlands.Cohomology.DivisibleSystem.HarrisEtale`) with Worker 57's
`HarrisCoefficientIntegers` (`Langlands.Shimura.Coefficients.HarrisLattice`)
and `IsFiniteGeometricTorsor` (`Langlands.Shimura.Coefficients.Etale`),
`harrisCongruenceGroups` (`Langlands.Shimura.Coefficients.HarrisReduction`)
and Worker 13's `EquivariantDiagram`
(`Langlands.CategoryTheory.EquivariantDiagram`), and Worker 3's unproved
statement
`MittagLefflerShortExactLimitStatement`
(`Langlands.Cohomology.InverseLimit.Statement`), which appears only as a
hypothesis.

From Mathlib it uses `Abelian.epiDesc` and `Abelian.comp_epiDesc`,
`ShortComplex` with `ShortComplex.ShortExact`, `ShortExact.gIsCokernel`,
`ShortComplex.Exact.lift`, `Exact.lift_f`, `Exact.epi_toCycles`,
`ShortComplex.exact_iff_mono_cokernel_desc`,
`ShortComplex.exact_iff_epi_kernel_lift`,
`ShortComplex.exact_iff_of_epi_of_isIso_of_mono`,
`ShortComplex.exact_of_f_is_kernel`, `ShortComplex.isoMk`,
`ShortComplex.exact_of_iso`, `toCycles`, `iCycles`, `cyclesIsKernel`,
`toCycles_i`, `cokernelIsCokernel`, `kernelIsKernel`,
`isLimitForkMapOfIsLimit'`, `IsLimit.conePointUniqueUpToIso`,
`IsColimit.coconePointUniqueUpToIso`, `Functor.rightDerived` with
`Functor.rightDerived_map_eq`, `InjectiveResolution.desc` and
`InjectiveResolution.desc_commutes`, `Monotone.functor`, `lim`, `limit.lift`,
`limit.pre`, `limit.pre_π`, `limit.lift_π`, `limit.w`, `limit.hom_ext`,
`limMap`, `limMap_π`, `limit.isoLimitCone`, `isLimitConstCone`,
`Functor.IsMittagLeffler`, `Functor.isMittagLeffler_of_exists_finite_range`
and `ModuleCat.mono_iff_injective`.

`levelShift`, `constLimitIso`, `constLimitIso_hom`,
`levelShiftLimitIso`, `levelShiftLimitIso_hom_π` and `limit_exact_of_finite`
are in the namespace `Langlands.Cohomology`; all other declarations are in
`Langlands.Cohomology.DivisibleSystem`.

## Conventions

Composition `f ≫ g` is `f` followed by `g`. `powSMul ℓ r M : M ⟶ M` is the
published multiplication by `ℓ ^ r`. For an object `M`, `M / ℓ ^ r` is the
cokernel of `powSMul ℓ r M` (with projection `reductionπ ℓ M r`) and
`M[ℓ ^ r]` its kernel; in Milne's notation these are `M^(ℓ^r)` and `M_{ℓ^r}`.
Here `m`, `r`, `n` are levels and `q` the cohomological degree; Milne's Lemma
1.11 writes `n` for the level and `r` for the degree.

`C` is an abelian category and `T : DivisibleSystem C ℓ` an `ℓ`-divisible
system, with levels `T m = T.obj m` and projections `T n ⟶ T m` for `m ≤ n`.
For the derived statements `C` has enough injectives, `D` is abelian,
`F : C ⥤ D` is additive and `R^q F = F.rightDerived q` is Mathlib's `q`-th
right derived functor. The published long exact sequence of right derived
functors needs derived categories of `C` and `D`; their
`HasDerivedCategory` instances are arguments. `lim_m R^q F(T m)` is the limit
of the inverse system `T.tower ⋙ F.rightDerived q`.

## General tools

- The imported instance
  `Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive F n`
  makes `F.rightDerived n` additive. Worker 958’s published proof is shared
  through `Langlands/Cohomology/RightDerivedAdditive`, with its original name
  and without algebraic-geometry imports. It computes the map of `f + g`
  through the sum of the chosen lifts to injective resolutions.
- `levelShift r : ℕ ⥤ ℕ`: the functor `m ↦ m + r`.
- `constLimitIso Z : lim_m Z ≅ Z` for the constant inverse system with value
  `Z` (`ℕᵒᵖ` is connected); `constLimitIso_hom`: its morphism is every limit
  projection.
- `levelShiftLimitIso X r : lim_m X(m + r) ≅ lim_m X(m)` for an inverse system
  `X : ℕᵒᵖ ⥤ D`. Its inverse is Mathlib's `limit.pre`;
  `levelShiftLimitIso_hom_π`: the projection to `X(m)` is the projection to
  `X(m + r)` followed by the transition map.
- `limit_exact_of_finite hML hS hfin`: for an exact sequence `X₁ ⟶ X₂ ⟶ X₃` of
  inverse systems of `R`-modules (`R` a ring) with every `X₁(m)` finite, given
  `hML : MittagLefflerShortExactLimitStatement R`,
  `lim X₁ ⟶ lim X₂ ⟶ lim X₃` is exact. Proof: the kernel `K` of
  `X₁ ⟶ ker(X₂ ⟶ X₃)` has finite levels, so it is Mittag-Leffler (Mathlib's
  `isMittagLeffler_of_exists_finite_range`). `hML` applied to
  `0 ⟶ K ⟶ X₁ ⟶ ker(X₂ ⟶ X₃) ⟶ 0` makes `lim X₁ ⟶ lim ker(X₂ ⟶ X₃)`
  surjective. Since `lim` preserves kernels, this is the map from `lim X₁` to
  the kernel of `lim X₂ ⟶ lim X₃`.

## Multiplication by ℓ^r between levels

Let `m + r = n`.

- `shortExact_inclusion_projection` and `flat_of_add_eq`: the published
  sequence `0 ⟶ T r ⟶ T n ⟶ T (n - r) ⟶ 0` and the published exact sequence
  `T n ⟶ T n ⟶ T n` of multiplications by `ℓ ^ a` and `ℓ ^ b`, restated with
  the indices `k = n - r` and `n = a + b` as variables.
- `kernel_ι_projection_comp_powSMul`: multiplication by `ℓ ^ r` on `T n` kills
  the kernel of the projection `T n ⟶ T m`. For `m = 0` it is zero on `T r`.
  For `m > 0` this kernel is the image of `i : T r ⟶ T n`, and
  `i ≫ ℓ ^ r = ℓ ^ r ≫ i = 0`.
- `powSMulMap h : T m ⟶ T n`: the factorization of multiplication by `ℓ ^ r`
  on `T n` through the epimorphism `T n ⟶ T m` (`Abelian.epiDesc`). For
  `T m = Λ / ℓ ^ m Λ` it is `x ↦ ℓ ^ r x`. `projection_comp_powSMulMap` and
  `powSMulMap_comp_projection`: `T n ⟶ T m ⟶ T n` and `T m ⟶ T n ⟶ T m` are
  multiplication by `ℓ ^ r`. `projection_comp_powSMulMap_comm`: `powSMulMap`
  commutes with the projections, for fixed `r`.
- `mono_powSMulMap` (instance): `powSMulMap` is a monomorphism. Proof: for
  `m > 0` the projection `T n ⟶ T m` is a cokernel of `i : T r ⟶ T n`, which
  is a kernel of `ℓ ^ r` (`torsion_exact`). So `powSMulMap` is the
  identification of `T m` with `coker i` followed by the monomorphism
  `coker i ⟶ T n` induced by `ℓ ^ r`.
- `powSMulShortComplex h`: the short complex `T m ⟶ T n ⟶ T r`, multiplication
  by `ℓ ^ r` (`powSMulMap`) and then the projection.
- `powSMulShortComplex_shortExact h`: `0 ⟶ T m ⟶ T n ⟶ T r ⟶ 0` is short
  exact. Proof: precomposing with the epimorphism `T n ⟶ T m` replaces
  `powSMulMap` by `ℓ ^ r`. Postcomposing with the monomorphism
  `powSMulMap : T r ⟶ T n` (for `r + m = n`) replaces the projection by
  `ℓ ^ m`. Exactness of `T n ⟶ T n ⟶ T n` (`flat`) then gives exactness by
  `exact_iff_of_epi_of_isIso_of_mono`.
- `powSMulShortComplexMap h h' hm hn`: for `m' ≤ m` (with `m' + r = n'`), the
  projections give a morphism from `T m ⟶ T n ⟶ T r` to `T m' ⟶ T n' ⟶ T r`
  that is the identity on `T r`.

## The finite-level sequence

Let `m + r = n`.

- `derivedReductionδ F h q : R^q F(T r) ⟶ R^(q+1) F(T m)`: the published
  connecting map of the long exact sequence of
  `0 ⟶ T m ⟶ T n ⟶ T r ⟶ 0`. `map_powSMulMap_comp_map_projection`,
  `map_projection_comp_derivedReductionδ` and
  `derivedReductionδ_comp_map_powSMulMap`: consecutive maps of
  `R^q F(T m) ⟶ R^q F(T n) ⟶ R^q F(T r) ⟶ R^(q+1) F(T m) ⟶ R^(q+1) F(T n)`
  compose to zero.
- `derivedReductionδ_comp_map_projection`: for `m' ≤ m`, `derivedReductionδ`
  for `m` followed by the map induced by `T m ⟶ T m'` is `derivedReductionδ`
  for `m'` (published naturality of the connecting maps, applied to
  `powSMulShortComplexMap`).
- `map_powSMulMap_comp_map_projection_eq`: the maps induced by `powSMulMap`
  and by the projection `T n ⟶ T m` compose to multiplication by `ℓ ^ r` on
  `R^q F(T m)`.
- `derivedReductionShortComplex F h q`: the short complex
  `coker R^q F(powSMulMap) ⟶ R^q F(T r) ⟶ ker R^(q+1) F(powSMulMap)`, the
  `cokernelKernelShortComplex` of the four maps above.
- `derivedReductionShortComplex_shortExact`: it is short exact, by the
  published exactness of the long exact sequence at its three middle terms.

## Milne's sequence for right derived functors

Here `D` has limits indexed by `ℕᵒᵖ`.

- `derivedPowSMulNatTrans F T r q`, `derivedReductionNatTrans F T r q` and
  `derivedReductionδNatTrans F T r q`: the maps `R^q F(T m) ⟶ R^q F(T (m + r))`
  induced by `powSMulMap`, the maps `R^q F(T (m + r)) ⟶ R^q F(T r)` induced by
  the projections (to the constant inverse system) and the connecting maps
  `R^q F(T r) ⟶ R^(q+1) F(T m)` (from the constant inverse system), as
  morphisms of inverse systems in `m`.
- `derivedAdicδ F T r q : R^q F(T r) ⟶ lim_m R^(q+1) F(T m)`: the map induced
  by the connecting maps; `derivedAdicδ_π`: its components are
  `derivedReductionδ`.
- `powSMul_limit_comp_π_eq_zero`, `π_comp_derivedAdicδ` and
  `derivedAdicδ_comp_powSMul`: in
  `lim_m R^q F(T m) ⟶ lim_m R^q F(T m) ⟶ R^q F(T r) ⟶ lim_m R^(q+1) F(T m) ⟶
  lim_m R^(q+1) F(T m)` (multiplication by `ℓ ^ r`, the limit projection,
  `derivedAdicδ`, multiplication by `ℓ ^ r`) consecutive maps compose to zero.
- `derivedAdicReductionSequence F T r q`: the short complex
  `(lim_m R^q F(T m)) / ℓ ^ r ⟶ R^q F(T r) ⟶ (lim_m R^(q+1) F(T m))[ℓ ^ r]`,
  the `cokernelKernelShortComplex` of these four maps. It is defined without
  hypotheses. `reductionπ_derivedAdicReductionSequence_f`: the first map after
  `reductionπ` is the limit projection. `derivedAdicReductionSequence_g_ι`:
  the second map followed by the inclusion of the `ℓ ^ r`-torsion is
  `derivedAdicδ`.
- `limMap_derivedPowSMulNatTrans_comp_levelShiftLimitIso`: under
  `levelShiftLimitIso`, the limit of the maps `R^q F(powSMulMap)` is
  multiplication by `ℓ ^ r` (by `map_powSMulMap_comp_map_projection_eq`).
  `limMap_derivedReductionNatTrans_comp_constLimitIso`: under the same
  identifications, the limit of the maps `R^q F(T (m + r)) ⟶ R^q F(T r)` is
  the limit projection. `limMap_derivedReductionδNatTrans`: under
  `constLimitIso`, the limit of the connecting maps is `derivedAdicδ`.
- `derivedAdicReductionSequence_shortExact F T hML r q hfin` (Milne, Lemma
  1.11, for right derived functors): for `D = ModuleCat R`, if every
  `R^q F(T m)` is finite (`hfin`), given
  `hML : MittagLefflerShortExactLimitStatement R`,
  `0 ⟶ (lim_m R^q F(T m)) / ℓ ^ r ⟶ R^q F(T r) ⟶
  (lim_m R^(q+1) F(T m))[ℓ ^ r] ⟶ 0` is short exact. Proof: the sequences of
  inverse systems `R^q F(T m) ⟶ R^q F(T (m + r)) ⟶ R^q F(T r)`,
  `R^q F(T (m + r)) ⟶ R^q F(T r) ⟶ R^(q+1) F(T m)` and
  `R^q F(T r) ⟶ R^(q+1) F(T m) ⟶ R^(q+1) F(T (m + r))` are exact levelwise
  (`powSMulShortComplex_shortExact` and the published long exact sequence).
  Their first terms are finite, so their limits are exact
  (`limit_exact_of_finite`). The three `limMap` lemmas identify these limit
  sequences with the three pieces of the four-term sequence, and
  `cokernelKernelShortComplex_shortExact` concludes. Only finiteness in
  degree `q` is used.

## Étale cohomology and Harris's ℓ-divisible system

`X : Scheme.{u}` is a scheme, `R : Type u` a commutative ring and
`T : DivisibleSystem (EtaleDerivedSections.ModuleSheaf X R) ℓ` an
`ℓ`-divisible system of sheaves of `R`-modules on the small étale site of
`X`. `H^q(X, -)` is Worker 13's `EtaleDerivedSections.cohomology X R q`, the
`q`-th right derived functor of the global sections functor
`EtaleDerivedSections.sections X R`.

- `etaleReductionSequence X R T r q`: `derivedAdicReductionSequence` for the
  global sections functor, the short complex
  `(lim_m H^q(X, T m)) / ℓ ^ r ⟶ H^q(X, T r) ⟶ (lim_m H^(q+1)(X, T m))[ℓ ^ r]`.
  `etaleReductionSequence_X₁`, `etaleReductionSequence_X₂` and
  `etaleReductionSequence_X₃` (by definition): its terms are the reduction
  modulo `ℓ ^ r` of the published
  `EtaleAdicCohomology.adicCohomology X R q` of `T.tower`, the published
  `EtaleDerivedSections.cohomology X R q` of `T r`, and the `ℓ ^ r`-torsion of
  `adicCohomology X R (q + 1)` of `T.tower`.
- `etaleReductionSequence_shortExact X R T hML r q hfin`: if every
  `H^q(X, T m)` is finite, given `MittagLefflerShortExactLimitStatement R`,
  `0 ⟶ (lim_m H^q(X, T m)) / ℓ ^ r ⟶ H^q(X, T r) ⟶
  (lim_m H^(q+1)(X, T m))[ℓ ^ r] ⟶ 0` is short exact.
- `harrisEtaleReductionSequence ℓ ρ p U X Y hY r q`: `etaleReductionSequence`
  for the published `harrisEtaleDivisibleSystem` of the étale sheaves
  `𝓛 / ℓ ^ m` over `HarrisCoefficientIntegers L p`.
  `harrisEtaleReductionSequence_X₁` and `harrisEtaleReductionSequence_X₃` (by
  definition): its outer terms are built from the published
  `EtaleAdicCohomology.harrisEtaleAdicCohomology` in degrees `q` and `q + 1`.
  `harrisEtaleReductionSequence_shortExact`: if every `H^q(X, 𝓛 / ℓ ^ m)` is
  finite, given `MittagLefflerShortExactLimitStatement` for
  `HarrisCoefficientIntegers L p`, it is short exact.

## Provenance and interpretation

Milne, *Étale Cohomology* (1980), Chapter V, §1 (Worker 61 read the scanned
pages, as recorded in the published `ReductionSequence`; printed p.165 in the
rendered image, the others in the text layer):

- printed p.165 (one-based PDF page 179), Lemma 1.11: "Let F = (F_n) be an
  l-adic sheaf on X_et such that each F_n is flat as a sheaf of
  Z/(l^n)-modules and H^r(X, F_n) is finite for all r and n. Then H^r(X, F) is
  finitely generated as a Z_l-module and there are exact sequences,
  0 → H^r(X_et, F)^(l^n) → H^r(X_et, F_n) → H^{r+1}(X_et, F)_{l^n} → 0 for
  all r and n." Milne's proof tensors
  `0 → Z/(l^n) → Z/(l^{n+s}) → Z/(l^s) → 0` with `F_{n+s}`, takes cohomology
  sequences and passes to the inverse limit, using that inverse limits of
  exact sequences of finite abelian groups are exact.
- printed p.164 (one-based PDF page 178): "The cohomology groups of an l-adic
  sheaf F are defined to be H^r(X, F) = lim H^r(X, F_n)."
- printed p.xiii (one-based PDF page 13), Notation: "The kernel and cokernel
  of multiplication by n, M → M, are denoted respectively by M_n and M^(n)."

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §2, printed p.304, (2.1), defines
`ℓ`-divisible systems; this is the published `DivisibleSystem`, and the
published `harrisEtaleDivisibleSystem` is one of étale sheaves.

Interpretation. The proof follows Milne's. With `m` for his `n` and `r` for
his `s`, the sequence `0 → F_m → F_{m+r} → F_r → 0` that he obtains by
tensoring with `F_{m+r}` and using flatness is here
`powSMulShortComplex_shortExact`. It is derived from the `DivisibleSystem`
axioms, which contain Milne's flatness hypothesis (`flat`). Milne's
`H^r(X, F) = lim_n H^r(X, F_n)` is `lim_m R^q F(T m)`, which for étale
cohomology is the published `adicCohomology`. His use of the exactness of
inverse limits of finite groups is `limit_exact_of_finite`. That lemma
assumes Worker 3's `MittagLefflerShortExactLimitStatement` (EGA III.0,
13.2.2), which is not proved here. Milne assumes finiteness in all degrees;
the proof uses only degree `q`. The general tools, the restated published
axioms, the morphisms of inverse systems and the `limMap` identifications are
internal framework. The statements and proofs are ours; the module is
derived.

## Scope

Finite generation of `lim_m H^q(X, T m)` over `ℤ_ℓ` is not formalized.
Neither the comparison with `H^q(X, lim_m T m)` nor any group, Hecke or
Galois action is treated, and the sequences are not shown to be natural in
`T`. The short exactness of the limit sequences assumes Worker 3's
`MittagLefflerShortExactLimitStatement` (`hML`) and the finiteness of the
level cohomology (`hfin`). No topology, continuity or `ℚ_ℓ`-coefficients are
treated.

Source registrations: Milne 1980, `milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`; Harris
1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
