# Reduction sequences for ℓ-adic limits of truncated Godement section systems

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.ReductionSequence` (Worker 61:
`cokernelKernelShortComplex`, `reductionShortComplex`, `reductionSequence`,
`reductionSequence_shortExact`, `reductionShortComplex_shortExact_moduleCat`,
`reductionShortComplex_shortExact_rep`, `homologyMap_powSMul` and
`powSMul_homology_eq_zero`; the construction of
`inverseLimitReductionSequence` is the pattern followed here) and
`Langlands.Cohomology.DivisibleSystem.ConstantInverseLimit` (Worker 61:
`adicLimit`, `levelCohomologyLimit`, `extendHomologyNatIso`,
`adicLimitComparison`, `adicLimitComparison_π`,
`isIso_adicLimitComparison_of_finite`, `isIso_adicLimitComparison_rep`,
`smoothGodementSectionsTower`, `smoothGodementTruncatedSectionsTowerHom`,
`smoothGodementTruncatedSectionsTowerHom_quasiIsoAt`,
`smoothGodementTruncatedSectionsAdicCohomologyIso` and
`smoothGodementTruncatedSectionsAdicCohomologyIso_hom_π`). Through their
imports it uses the published `DivisibleSystem` with `tower`, `obj` and
`projection`, `powSMul` and `comp_powSMul`
(`Langlands.Cohomology.DivisibleSystem`), `reductionπ`
(`Langlands.Cohomology.DivisibleSystem.Reduction`), `powSMul_comp_π`
(`Langlands.Cohomology.DivisibleSystem.AdicLimit`), `extendSystem`
(`Langlands.Cohomology.DivisibleSystem.TotalComparison`),
`smoothGodementTermSystem` and `smoothGodementResidualSystem`
(`Langlands.Cohomology.DivisibleSystem.Coaugmented`),
`smoothGodementTruncatedSectionsSystem`
(`Langlands.Cohomology.DivisibleSystem.ConstantTruncation`), the published
`SmoothSheafDivisibleSystem`, Worker 13's `SmoothTopologicalSheaf` and
`HasStableNeighbourhoods`, and Worker 3's unproved statements
`SmoothGodementZeroExactStatement`
(`Langlands.Cohomology.SmoothGodement.Statement`) and
`FiniteCohomologyInverseLimitStatement`
(`Langlands.Cohomology.InverseLimit.Statement`), which appear only as
hypotheses.

From Mathlib it uses `ShortComplex`, `ShortComplex.ShortExact` with
`ShortExact.δ`, `ShortExact.comp_δ` and `ShortExact.δ_comp`,
`ShortComplex.isoMk`, `ShortComplex.shortExact_of_iso`, `cokernel.mapIso`,
`kernel.mapIso`, `cokernel.π_desc`, `kernel.lift_ι`,
`HomologicalComplex.homologyMap` with `homologyMap_comp` and
`homologyMap_zero`, `HomologicalComplex.homologyFunctor`, `limit.cone`,
`limit.π`, `cancel_epi`, `asIso` and `ComplexShape.up`.

`comp_eq_zero_of_iso` and `cokernelKernelShortComplexIso` are in the
namespace `Langlands.Cohomology`; all other declarations are in
`Langlands.Cohomology.DivisibleSystem`.

## Conventions

Composition `f ≫ g` is `f` followed by `g`. `powSMul ℓ r M : M ⟶ M` is the
published multiplication by `ℓ ^ r`. For an object `M`, `M / ℓ ^ r` is the
cokernel of `powSMul ℓ r M` (with projection `reductionπ ℓ M r`) and
`M[ℓ ^ r]` its kernel; in Milne's notation these are `M^(ℓ^r)` and
`M_{ℓ^r}`. Here `r` is the level and `n` the cohomological degree; Milne's
Lemma 1.11 writes `n` for the level and `r` for the degree.

`E` is an abelian category and `K : DivisibleSystem (CochainComplex E ℕ) ℓ`
an `ℓ`-divisible system of `ℕ`-graded cochain complexes, with levels
`K r = K.obj r`. `H^n(X)` is the degree-`n` cohomology `X.homology n`. When
`E` has limits indexed by `ℕᵒᵖ`, the published `adicLimit K` is the limit
`lim_m K m` of the levels extended by zero to `ℤ` (`K.extendSystem`),
`levelCohomologyLimit K n` is `lim_m H^n(K m)`, and
`adicLimitComparison K n : H^n(adicLimit K) ⟶ lim_m H^n(K m)` is the
published comparison (Harris's Lemma 2.8 map). In this section the
hypothesis

`hS : (reductionShortComplex (limit.cone K.extendSystem.tower) r).ShortExact`

says that `0 ⟶ adicLimit K ⟶ adicLimit K ⟶ K r ⟶ 0` (multiplication by
`ℓ ^ r`, then the projection, with `K r` extended to `ℤ`) is short exact. The
connecting map `hS.δ` of Mathlib goes from `H^n` of the extended level `r`
to `H^{n+1}(adicLimit K)`.

## Transport along isomorphisms

`C` is an abelian category.

- `comp_eq_zero_of_iso eX eY eZ wf wg hfg`: if `f ≫ g = 0` and isomorphisms
  `eX`, `eY`, `eZ` satisfy `f ≫ eY.hom = eX.hom ≫ f'` and
  `g ≫ eZ.hom = eY.hom ≫ g'`, then `f' ≫ g' = 0`.
- `cokernelKernelShortComplexIso eA eB eX eD eE wf wg wδ wh`: isomorphisms
  between two sequences `A ⟶ B ⟶ X ⟶ D ⟶ E` and `A' ⟶ B' ⟶ X' ⟶ D' ⟶ E'`
  commuting with the four maps induce an isomorphism of the published short
  complexes `cokernelKernelShortComplex` (`coker f ⟶ X ⟶ ker h`). Its
  components are `cokernel.mapIso`, `eX` and `kernel.mapIso`.

## Milne's sequence for `ℓ`-adic limits

`E` has limits indexed by `ℕᵒᵖ` and `K` is as in the conventions.

- `levelExtendHomologyIso K r n` (`abbrev`): the degree-`n` cohomology of the
  extension by zero of `K r` is `H^n(K r)`, the component of the published
  `extendHomologyNatIso`.
- `up_int_rel_natCast n`: in `ComplexShape.up ℤ`, the differential goes from
  degree `n` to degree `n + 1` (for `n : ℕ`, cast to `ℤ`).
- `powSMul_comp_levelCohomologyLimit_π K r n`: multiplication by `ℓ ^ r` on
  `lim_m H^n(K m)` followed by the projection to `H^n(K r)` is zero (the
  published `powSMul_homology_eq_zero`).
- `adicReductionSequence hS n`: the short complex
  `H^n(adicLimit K) / ℓ ^ r ⟶ H^n(K r) ⟶ H^{n+1}(adicLimit K)[ℓ ^ r]`, the
  `cokernelKernelShortComplex` of `ℓ ^ r`, the map induced on `H^n` by the
  limit projection followed by `levelExtendHomologyIso`, the inverse of
  `levelExtendHomologyIso` followed by the connecting map `hS.δ`, and
  `ℓ ^ r`.
- `reductionSequenceAdicIso hS n`: the published `reductionSequence` of the
  limit cone of `K.extendSystem` (in degrees `n` and `n + 1`) is isomorphic to
  `adicReductionSequence hS n` (identities, except `levelExtendHomologyIso`
  in the middle).
- `reductionπ_adicReductionSequence_f`, `adicReductionSequence_g_ι`: the
  projection to the cokernel followed by the first map is the map induced by
  the limit projection followed by `levelExtendHomologyIso`; the second map
  followed by the inclusion of the `ℓ ^ r`-torsion is the inverse of
  `levelExtendHomologyIso` followed by the connecting map.
- `adicReductionSequence_shortExact hS n` (Milne, Lemma 1.11, for
  `H^n(adicLimit K)`): `0 ⟶ H^n(adicLimit K) / ℓ ^ r ⟶ H^n(K r) ⟶
  H^{n+1}(adicLimit K)[ℓ ^ r] ⟶ 0` is short exact. Proof: the published
  `reductionSequence_shortExact`, transported along
  `reductionSequenceAdicIso`.
- `homologyMap_π_comp_δ hS n`: the map induced by the limit projection,
  followed by the connecting map (through `levelExtendHomologyIso`), is zero.

Now let `hn : IsIso (K.adicLimitComparison n)`.

- `levelCohomologyLimit_π_comp_δ hS n hn`: the projection
  `lim_m H^n(K m) ⟶ H^n(K r)`, followed by the connecting map and
  `adicLimitComparison K (n + 1)`, is zero. Proof: precompose with the
  epimorphism `adicLimitComparison K n`; by `adicLimitComparison_π` the
  composite becomes the one of `homologyMap_π_comp_δ`.
- `δ_comp_powSMul_levelCohomologyLimit hS n`: the connecting map followed by
  `adicLimitComparison K (n + 1)` and `ℓ ^ r` on `lim_m H^{n+1}(K m)` is zero
  (`ℓ ^ r` commutes with the comparison, and `hS.δ` followed by the map
  induced by `ℓ ^ r` is zero).
- `adicLevelReductionSequence hS n hn`: the short complex
  `(lim_m H^n(K m)) / ℓ ^ r ⟶ H^n(K r) ⟶ (lim_m H^{n+1}(K m))[ℓ ^ r]`, the
  `cokernelKernelShortComplex` of `ℓ ^ r`, the projection
  `lim_m H^n(K m) ⟶ H^n(K r)`, the connecting map (through
  `levelExtendHomologyIso`) followed by `adicLimitComparison K (n + 1)`, and
  `ℓ ^ r`. The hypothesis `hn` is used only for the vanishing of the composite
  of the middle two maps.
- `reductionπ_adicLevelReductionSequence_f`,
  `adicLevelReductionSequence_g_ι`: the projection to the cokernel followed by
  the first map is the projection `lim_m H^n(K m) ⟶ H^n(K r)`; the second map
  followed by the inclusion of the torsion is the connecting map followed by
  the comparison in degree `n + 1`.
- `adicReductionSequenceLevelIso hS n hn hn'`: if moreover
  `hn' : IsIso (K.adicLimitComparison (n + 1))`, then
  `adicReductionSequence hS n ≅ adicLevelReductionSequence hS n hn`, through
  the comparisons in degrees `n` and `n + 1` and the identity of `H^n(K r)`.
- `adicLevelReductionSequence_shortExact hS n hn hn'` (Milne, Lemma 1.11,
  with `H^n = lim_m H^n(K m)`): under `hn` and `hn'`,
  `0 ⟶ (lim_m H^n(K m)) / ℓ ^ r ⟶ H^n(K r) ⟶
  (lim_m H^{n+1}(K m))[ℓ ^ r] ⟶ 0` is short exact.
- `adicLevelReductionSequence_shortExact_of_finite hF K hfin r n`: for
  `K : DivisibleSystem (CochainComplex (ModuleCat R) ℕ) ℓ` (`R` commutative)
  whose levels have finite cohomology in every degree (`hfin`), given
  `hF : FiniteCohomologyInverseLimitStatement R`, the previous sequence is
  short exact, with `hS` the published
  `reductionShortComplex_shortExact_moduleCat` of `K.extendSystem` and the
  comparisons made isomorphisms by `isIso_adicLimitComparison_of_finite`.
- `adicLevelReductionSequence_shortExact_rep hF K hfin r n`: the same for
  `K : DivisibleSystem (CochainComplex (Rep k G) ℕ) ℓ` (`k` commutative, `G`
  a monoid) with finite cohomology, given
  `hF : FiniteCohomologyInverseLimitStatement k`, as a short exact sequence of
  representations (`reductionShortComplex_shortExact_rep`,
  `isIso_adicLimitComparison_rep`).

## Truncated smooth Godement section systems

`R` is a commutative ring, `G` a topological group, `X` a topological space
with a `G`-action by homeomorphisms and `HasStableNeighbourhoods G X`, all in
one universe. `h : SmoothGodementZeroExactStatement R G X`,
`T : SmoothSheafDivisibleSystem R G X ℓ`, `D : ℕ`, and
`Φ : SmoothTopologicalSheaf R G X ⥤ E` is an additive functor preserving
finite limits (a sections functor). `hterm` and `hres` say that `Φ` maps the
projections of the smooth Godement term systems `F^q` (`q ≤ D`) and of the
residual system `R^(D + 1)` to epimorphisms. Write
`K_D = smoothGodementTruncatedSectionsSystem h T D Φ hterm hres` for the
published system of section complexes `Φ(G_m^•)` of the truncated
resolutions `G_m^• = τ^{≤D+1}(F_m^•)` (Harris's `G_m^•(U)`), and `Φ(F_m^•)`
for the level `m` of the published tower `smoothGodementSectionsTower h T Φ`
of section complexes of the full smooth Godement resolutions.

- `smoothGodementTruncatedSectionsLevelHomologyIso h T D Φ hterm hres r hn`,
  for `hn : n ≤ D + 1`: `H^n(Φ(G_r^•)) ≅ H^n(Φ(F_r^•))`, the map induced on
  cohomology by the inclusion `smoothGodementTruncatedSectionsTowerHom`
  (`smoothGodementTruncatedSectionsLevelHomologyIso_hom`, by definition),
  which is a quasi-isomorphism in degree `n` by the published
  `smoothGodementTruncatedSectionsTowerHom_quasiIsoAt`.
- `π_smoothGodementTruncatedSectionsLevelHomologyIso_hom` (with
  `E` having limits indexed by `ℕᵒᵖ`): the projections
  `lim_m H^n(Φ(G_m^•)) ⟶ H^n(Φ(G_r^•))` and
  `lim_m H^n(Φ(F_m^•)) ⟶ H^n(Φ(F_r^•))` commute with the published
  `smoothGodementTruncatedSectionsAdicCohomologyIso` and
  `smoothGodementTruncatedSectionsLevelHomologyIso`.

From here on `E` has limits indexed by `ℕᵒᵖ`, `hS` is the short exactness
hypothesis of the conventions for `K = K_D`, and `hn : n ≤ D`.

- `smoothGodementReductionδ hS n hn : H^n(Φ(F_r^•)) ⟶ lim_m H^{n+1}(Φ(F_m^•))`:
  the inverse of `smoothGodementTruncatedSectionsLevelHomologyIso` (degree
  `n`), the inverse of `levelExtendHomologyIso`, the connecting map `hS.δ`,
  `adicLimitComparison K_D (n + 1)`, and
  `smoothGodementTruncatedSectionsAdicCohomologyIso` in degree `n + 1`.
- `smoothGodementReductionδ_comm hS n hn`: the second map of
  `adicLevelReductionSequence` for `K_D`, followed by
  `smoothGodementTruncatedSectionsAdicCohomologyIso` in degree `n + 1`, is
  `smoothGodementTruncatedSectionsLevelHomologyIso` followed by
  `smoothGodementReductionδ`.

Let `hcmp : IsIso (K_D.adicLimitComparison n)`.

- `smoothGodementReductionSequence hS n hn hcmp`: the short complex
  `(lim_m H^n(Φ(F_m^•))) / ℓ ^ r ⟶ H^n(Φ(F_r^•)) ⟶
  (lim_m H^{n+1}(Φ(F_m^•)))[ℓ ^ r]`, the `cokernelKernelShortComplex` of
  `ℓ ^ r`, the projection `lim_m H^n(Φ(F_m^•)) ⟶ H^n(Φ(F_r^•))`,
  `smoothGodementReductionδ` and `ℓ ^ r`. The vanishing of the three
  composites is transported by `comp_eq_zero_of_iso` from the corresponding
  facts for `K_D` (`powSMul_comp_levelCohomologyLimit_π`,
  `levelCohomologyLimit_π_comp_δ`, which uses `hcmp`, and
  `δ_comp_powSMul_levelCohomologyLimit`).
- `reductionπ_smoothGodementReductionSequence_f`,
  `smoothGodementReductionSequence_g_ι`: the projection to the cokernel
  followed by the first map is the projection
  `lim_m H^n(Φ(F_m^•)) ⟶ H^n(Φ(F_r^•))`; the second map followed by the
  inclusion of the torsion is `smoothGodementReductionδ`.
- `adicLevelReductionSequenceSmoothGodementIso hS n hn hcmp`:
  `adicLevelReductionSequence hS n hcmp ≅ smoothGodementReductionSequence hS n
  hn hcmp`, through `smoothGodementTruncatedSectionsAdicCohomologyIso` in
  degrees `n` and `n + 1` and `smoothGodementTruncatedSectionsLevelHomologyIso`.
- `smoothGodementReductionSequence_shortExact hS n hn hcmp hcmp'` (Milne,
  Lemma 1.11, for Harris's truncated section systems): if moreover
  `hcmp' : IsIso (K_D.adicLimitComparison (n + 1))`, then
  `0 ⟶ (lim_m H^n(Φ(F_m^•))) / ℓ ^ r ⟶ H^n(Φ(F_r^•)) ⟶
  (lim_m H^{n+1}(Φ(F_m^•)))[ℓ ^ r] ⟶ 0` is short exact, for `n ≤ D`. Proof:
  `adicLevelReductionSequence_shortExact` transported along
  `adicLevelReductionSequenceSmoothGodementIso`.
- `smoothGodementReductionSequence_shortExact_of_finite h T D Φ hterm hres hF
  hfin r n hn`: for `Φ` with values in `ModuleCat R'` (`R'` commutative),
  given `hF : FiniteCohomologyInverseLimitStatement R'` and finite cohomology
  of every level of `K_D` in every degree (`hfin`), the sequence above is
  short exact for `n ≤ D`, with `hS` the published
  `reductionShortComplex_shortExact_moduleCat` and the comparisons made
  isomorphisms by `isIso_adicLimitComparison_of_finite`.
- `smoothGodementReductionSequence_shortExact_rep h T D Φ hterm hres hF hfin r
  n hn`: the same for `Φ` with values in `Rep k G'` (`k` commutative, `G'` a
  monoid), given `hF : FiniteCohomologyInverseLimitStatement k`
  (`reductionShortComplex_shortExact_rep`, `isIso_adicLimitComparison_rep`).

The published constant section systems
`constantGodementTruncatedSectionsSystem` (levels `R / ℓ ^ m R`) and
`intConstantGodementTruncatedSectionsSystem` (levels `ℤ / ℓ ^ m ℤ`) are
abbreviations for `smoothGodementTruncatedSectionsSystem` with `T` the
constant systems `constantSheafSystem hℓ G X` and
`intConstantSheafSystem ℓ hℓ G X`, so the results of this section apply to
them; there are no separate declarations. Worker 61 checked in a private Lean
probe that `smoothGodementReductionSequence_shortExact_of_finite` applies to
`constantGodementTruncatedSectionsSystem`.

## Provenance and interpretation

Milne, *Étale Cohomology* (1980), Chapter V, §1 (Worker 61 read the scanned
pages; printed p.165 in the rendered image, the others in the text layer):

- printed p.165 (one-based PDF page 179), Lemma 1.11: "Let F = (F_n) be an
  l-adic sheaf on X_et such that each F_n is flat as a sheaf of
  Z/(l^n)-modules and H^r(X, F_n) is finite for all r and n. Then H^r(X, F) is
  finitely generated as a Z_l-module and there are exact sequences,
  0 → H^r(X_et, F)^(l^n) → H^r(X_et, F_n) → H^{r+1}(X_et, F)_{l^n} → 0 for
  all r and n."
- printed p.164 (one-based PDF page 178): "The cohomology groups of an l-adic
  sheaf F are defined to be H^r(X, F) = lim H^r(X, F_n)."
- printed p.xiii (one-based PDF page 13), Notation: "The kernel and cokernel
  of multiplication by n, M → M, are denoted respectively by M_n and M^(n)."

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306 (one-based
PDF pages 7–8; Worker 61 read both pages in the scanned original):

- p.305: Harris sets `G_m^• = τ^{≤D+1}(F_m^•)` and notes that "it follows
  from Fact 2 that, for any m, the inclusion τ^{≤q}(F_m^•) → (F_m^•) is a
  quasi-isomorphism for q ≥ D". With `Z_m^q = ker d_m^q` and
  `B_m^q = im d_m^{q-1}` on the section complexes he writes
  "(2.3) H_c^q(U(ẽ)_F̄, Z/ℓ^mZ) ≅ Z_m^q/B_m^q = H^q(G_m^•(U(ẽ)_F̄))".
- p.306: "Lemma 2.8. For every q, there is a canonical isomorphism
  H^q(lim C_m^•(U(ẽ)_F̄)) ≅ lim H_c^q(U(ẽ)_F̄, Z/ℓ^mZ)."

Interpretation. This module combines two published results of Worker 61:
Milne's sequence for the inverse limit of an `ℓ`-divisible system of
complexes (`ReductionSequence`, proved through the homology sequence of
`0 → L → L → T r → 0`, not by Milne's tensor-product argument) and the
`ℓ`-adic limits of the truncated smooth Godement section systems with their
comparison maps (`ConstantInverseLimit`). With `H^n = lim_m H^n(Φ(F_m^•))` as
in Milne's definition on p.164, `smoothGodementReductionSequence_shortExact`
is Lemma 1.11 for the systems `{Φ(G_m^•)}` in degrees `n ≤ D`. The degree
bound comes from the published isomorphisms
`H^q(Φ(G_m^•)) ≅ H^q(Φ(F_m^•))` for `q ≤ D + 1`, which are our elementary
observation (using that `Φ` is left exact) and not Harris's Fact 2 argument
(see the published `ConstantInverseLimit`). As there, `H^n(Φ(F_m^•))` (for
`Φ` the compact sections) stands for Harris's `H_c^n(U, ℤ/ℓ^mℤ)`; this is an
interpretation, and Harris's (2.3) is not formalized. The `ℓ`-adic limit of
`ℕ`-graded systems extended by zero to `ℤ`, the transport lemmas and the
separate connecting map `smoothGodementReductionδ` are internal framework.
Milne's flatness hypothesis corresponds to the published `DivisibleSystem`
axioms. The comparison isomorphisms are hypotheses, or are derived from
Worker 3's `FiniteCohomologyInverseLimitStatement` with finite level
cohomology, in place of Harris's Mittag-Leffler argument. The statements and
proofs are ours; the module is derived.

## Scope

No étale or `ℓ`-adic sheaf appears, and finite generation over `ℤ_ℓ` is not
formalized. Degrees `n > D` of the truncated systems are not treated. These
remain explicit hypotheses: `SmoothGodementZeroExactStatement` (`h`); the
surjectivity of the sections functors on the projections (`hterm`, `hres`);
in the general statements the short exactness `hS` of
`0 → lim → lim → K r → 0` and the comparison isomorphisms (`hn`, `hn'`,
`hcmp`, `hcmp'`); and in the module and representation cases
`FiniteCohomologyInverseLimitStatement` (`hF`) and the finiteness of the level
cohomology (`hfin`). No topology, continuity or `ℚ_ℓ`-coefficients are
treated.

Source registrations: Milne 1980, `milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`; Harris
1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
