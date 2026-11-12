# Acyclic truncated resolutions of ℓ-divisible systems (Harris 1999, Lemma 2.2 bis and (2.3))

Author: Worker 26. This is a generic module. It completes Worker 61's published truncated
resolution systems with their augmentations, their `Φ`-acyclicity, and Harris's
identification (2.3) of the cohomology of the section complexes with right derived functors.
It uses the following published modules:

- `Langlands.Cohomology.DivisibleSystem` (Worker 61): `DivisibleSystem`, `obj`,
  `projection`, `shortExact`, `isZero_obj_zero` and `shortComplex_exact_congr`.
- `Langlands.Cohomology.DivisibleSystem.Coaugmented` (Worker 61): `residualSystem`,
  `termSystem`, `residualInclusion`, `mono_residualInclusion_tower_app`,
  `residual_shortExact`, `residualInclusion_termDifferential_tower_app` and
  `residualInclusion_termDifferential_exact`.
- `Langlands.Cohomology.DivisibleSystem.Resolution` (Worker 61): `resolutionSystem`,
  `resolutionSystem_obj_d` and `resolutionSystem_obj_exactAt`.
- `Langlands.Cohomology.DivisibleSystem.Truncation` (Worker 61): `truncatedResolutionSystem`,
  `truncatedResolutionHom` (with its published instance `truncatedResolutionHom_quasiIso`),
  `isZero_truncatedResolutionSystem_obj_X`, `truncationTerm`, `truncationTerm_of_le`,
  `truncationTerm_of_eq`, `isZero_truncationTerm_tower_obj`,
  `isIso_truncationInclusion_tower_app` and `mono_truncationInclusion_tower_app`.
- `Langlands.Cohomology.DivisibleSystem.LeftExact` (Worker 61): `epi_map_projection_of_succ`.
- `Langlands.Cohomology.DivisibleSystem.Sections` (Worker 61):
  `truncatedResolutionSectionsSystem`.
- `Langlands.Cohomology.RightDerivedSequence`: `DerivedPlus.rightDerived_exact₃` and
  `DerivedPlus.shortExact_map_of_isZero_rightDerived_one` (the long exact sequence of the
  right derived functors `Functor.rightDerived`).
- `Langlands.Cohomology.AcyclicResolution.Comparison`: `AcyclicResolution.resolutionComparison`
  and `AcyclicResolution.comp_lift_id`.
- `Langlands.Cohomology.AcyclicResolution.ComparisonProof`:
  `acyclicResolutionComparisonStatement` (the proof of the published
  `AcyclicResolutionComparisonStatement`) and
  `AcyclicComparison.isZero_rightDerived_obj_of_isZero`.

From Mathlib it uses `CochainComplex.fromSingle₀Equiv` (with
`CochainComplex.fromSingle₀Equiv_symm_apply_f_zero`), `CochainComplex.quasiIsoAt₀_iff`,
`ShortComplex.quasiIso_iff_of_zeros`, `quasiIsoAt_iff_exactAt`,
`CochainComplex.exactAt_succ_single_obj`, `quasiIso_of_comp_right`, `asIso` and
`HasDerivedCategory.standard`.

All names are in the namespace `Langlands.Cohomology.DivisibleSystem`.

## Setting

`C` is an abelian category. `F : C ⥤ C` is additive and exact (instances
`[PreservesFiniteLimits F]` and `[PreservesFiniteColimits F]`), and `η : 𝟭 C ⟶ F` is a
coaugmentation with every component monic. `T : DivisibleSystem C ℓ` is an `ℓ`-divisible
system in the published sense: levels `T m`, inclusions `T m' ⟶ T m`, projections
`T m ⟶ T (m - m')`, short exact sequences `0 ⟶ T m' ⟶ T m ⟶ T (m - m') ⟶ 0`, and `T 0`
zero. `D : ℕ` is the truncation degree.

Worker 61's published constructions give the residual systems `R q` (`R 0 = T`,
`R (q + 1) = coker (R q ⟶ F(R q))`), the term systems `F^q = F(R q)`, the resolution system
`F^•` whose level `m` is the complex `F^0_m ⟶ F^1_m ⟶ ⋯`, and Harris's truncation
`G^• = τ_{≤ D+1}(F^•)` (`truncatedResolutionSystem F η T D`). `G^q = F^q` for `q ≤ D`,
`G^{D+1} = R (D + 1)`, and `G^q = 0` for `q > D + 1`. `truncatedResolutionHom` is the
inclusion `G^• ⟶ F^•`; at each level it is a quasi-isomorphism.

In the section `Acyclic`, `C` also has enough injectives. `E` is an abelian category and
`Φ : C ⥤ E` is an additive functor. It stands for Harris's compact sections
`Γ_c(U(ẽ)_F̄, -)`. The right derived functors are Mathlib's `Φ.rightDerived n`, computed with
injective resolutions.

## Hypotheses

The section `Acyclic` takes two explicit hypotheses. Nothing here proves them.

- `hF : ∀ M r, IsZero ((Φ.rightDerived (r + 1)).obj (F.obj M))`: every value of `F` is
  `Φ`-acyclic. This is Harris's statement that `F(T)` is acyclic for `RΓ_c` (p.304).
- `hT : ∀ m n, D < n → IsZero ((Φ.rightDerived n).obj (T.obj m))`: the right derived functors
  of `Φ` vanish on every level of `T` above degree `D`. This is the case `U = U(ẽ)` of Harris's
  Fact 2 (p.303), for the levels of `T`.

From `epi_map_termSystem_projection` on, `Φ` is also left exact
(`[PreservesFiniteLimits Φ]`), as the published sections system and the comparison theorem
require. `epi_map_projection_of_isZero_rightDerived_one` takes this instance as its own
argument.

## Declarations

Section `Augmentation` (no `Φ`):

- `resolutionSystemAugmentation F η T m`: the augmentation `T m ⟶ F^•_m`, a cochain map from
  `T m` placed in degree `0`. Its degree-zero component is the published
  `residualInclusion F η 0` at level `m`, the embedding `b_m : T m ⟶ F(T m)`
  (`resolutionSystemAugmentation_f_zero`).
- `resolutionSystemAugmentation_quasiIso` (instance): this augmentation is a
  quasi-isomorphism. Level `m` of `F^•` is a resolution of `T m`.
- `isIso_truncatedResolutionHom_f_zero` (instance): in degree `0` the inclusion `G^•_m ⟶ F^•_m`
  is an isomorphism.
- `comp_inv_comp_eq_zero_of_comm`: an auxiliary identity. Let `g₀` be an isomorphism and `g₁`
  a monomorphism with `g₀ ≫ d = d' ≫ g₁`. If `a ≫ d = 0`, then `(a ≫ g₀⁻¹) ≫ d' = 0`.
- `truncatedResolutionAugmentation F η T D m`: the augmentation `T m ⟶ G^•_m`. Its
  degree-zero component is that of `resolutionSystemAugmentation` followed by the inverse of
  the degree-zero inclusion (`truncatedResolutionAugmentation_f_zero`).
- `truncatedResolutionAugmentation_comp` (`simp`, `reassoc`): composed with the inclusion
  `G^•_m ⟶ F^•_m`, it gives `resolutionSystemAugmentation`.
- `truncatedResolutionAugmentation_quasiIso` (instance): this augmentation is a
  quasi-isomorphism. Level `m` of `G^•` is a finite-length resolution of `T m`. This is the
  resolution part of Lemma 2.2 bis, without acyclicity.

Section `Acyclic`:

- `epi_map_projection_of_isZero_rightDerived_one`: let `Φ` be left exact and `S` an
  `ℓ`-divisible system with `R^1 Φ (S m) = 0` for every `m`. Then `Φ` maps every projection
  `S m ⟶ S m'` (`m' ≤ m`) to an epimorphism.
- `isZero_rightDerived_residualSystem_obj` (needs `hF`, `hT`): `Rⁿ Φ` vanishes on every level
  of `R q` when `n > 0` and `n + q > D`.
- `isZero_rightDerived_residualSystem_succ_obj`: in particular every level of `R (D + 1)` is
  `Φ`-acyclic.
- `isZero_rightDerived_truncatedResolutionSystem_obj_X`: every term of every level of `G^•`
  is `Φ`-acyclic. With `truncatedResolutionAugmentation_quasiIso`, this makes level `m` of
  `G^•` a `Φ`-acyclic resolution of `T m` of finite length. This is Lemma 2.2 bis for `T`,
  without the divisible-system condition on the section side.
- `epi_map_termSystem_projection` (needs `hF`, left exact `Φ`): `Φ` maps the projections of
  every `F^q` to epimorphisms.
- `epi_map_residualSystem_succ_projection` (needs `hF`, `hT`, left exact `Φ`): `Φ` maps the
  projections of `R (D + 1)` to epimorphisms. This is the surjectivity Harris checks for
  `G^{D+1}`.
- `acyclicTruncatedSectionsSystem Φ F η T D hF hT`: the `ℓ`-divisible system of finite-length
  complexes `Φ(G^•_m)`. It is the published `truncatedResolutionSectionsSystem` with the two
  epimorphism conditions supplied by the previous lemmas. `acyclicTruncatedSectionsSystem_obj`
  states that level `m` is `Φ` applied degreewise to `G^•_m` (by `rfl`).
- `isZero_acyclicTruncatedSectionsSystem_obj_X`: every level is zero in degrees above `D + 1`.
- `isIso_truncatedResolutionComparison` (lemma, needs `hF`, `hT`): the published comparison
  map `AcyclicResolution.resolutionComparison Φ (truncatedResolutionAugmentation F η T D m) n`
  from `Hⁿ(Φ(G^•_m))` to `Rⁿ Φ (T m)` is an isomorphism.
- `acyclicTruncatedSectionsHomologyIso Φ F η T D hF hT m n`: Harris's (2.3), the isomorphism
  `Hⁿ(Φ(G^•_m)) ≅ Rⁿ Φ (T m)` given by this comparison map. Its inverse goes in the direction
  `Rⁿ Φ (T m) ⥲ Hⁿ(Φ(G^•_m))` printed by Harris. `acyclicTruncatedSectionsHomologyIso_hom`
  states that the forward map is the comparison map (by `rfl`).
- `isZero_acyclicTruncatedSectionsSystem_homology`: `Hⁿ(Φ(G^•_m)) = 0` for `n > D`.

## Proofs

- Quasi-isomorphism of `resolutionSystemAugmentation`: in degree `0` it reduces to exactness
  of `T m ⟶ F^0_m ⟶ F^1_m` (published `residualInclusion_termDifferential_exact`) and the
  monomorphism `T m ⟶ F^0_m`. In positive degrees it reduces to exactness of `F^•_m`
  (published `resolutionSystem_obj_exactAt`) and of the single complex.
- `truncatedResolutionAugmentation` is built with `CochainComplex.fromSingle₀Equiv`. The
  vanishing of its composite with the degree-zero differential is
  `comp_inv_comp_eq_zero_of_comm`, applied to the commutative square of the inclusion
  `G^•_m ⟶ F^•_m` in degrees `0, 1`. Its quasi-isomorphism property follows from
  `truncatedResolutionAugmentation_comp`, the published quasi-isomorphism of the inclusion,
  and two-out-of-three (`quasiIso_of_comp_right`).
- `epi_map_projection_of_isZero_rightDerived_one`: by the published
  `epi_map_projection_of_succ` it suffices to treat `S (k + 1) ⟶ S k`. For `k = 0` the target
  `Φ (S 0)` is zero. Otherwise `0 ⟶ S 1 ⟶ S (k + 2) ⟶ S (k + 1) ⟶ 0` is short exact, and `Φ`
  keeps it short exact because `R^1 Φ (S 1) = 0`
  (`DerivedPlus.shortExact_map_of_isZero_rightDerived_one`).
- `isZero_rightDerived_residualSystem_obj` is dimension shifting by induction on `q`. The case
  `q = 0` is `hT`. For `q + 1` and `n = r + 1`, the exact sequence
  `R^{r+1} Φ (F(R q)_m) ⟶ R^{r+1} Φ (R (q + 1)_m) ⟶ R^{r+2} Φ (R q _m)` of the short exact
  sequence `0 ⟶ R q ⟶ F^q ⟶ R (q + 1) ⟶ 0` (published `residual_shortExact`,
  `DerivedPlus.rightDerived_exact₃`) has zero outer terms, by `hF` and by induction.
- `isZero_rightDerived_truncatedResolutionSystem_obj_X` treats the three cases `i ≤ D`
  (`hF`), `i = D + 1` (the previous lemma) and `i > D + 1` (zero term).
- `epi_map_termSystem_projection` and `epi_map_residualSystem_succ_projection` apply
  `epi_map_projection_of_isZero_rightDerived_one` with `hF` and with
  `isZero_rightDerived_residualSystem_succ_obj`.
- `isIso_truncatedResolutionComparison` applies the published
  `acyclicResolutionComparisonStatement` to the augmentation of `G^•_m`, its acyclic terms,
  Mathlib's chosen injective resolution of `T m` and the published lift with
  `AcyclicResolution.comp_lift_id`. The second component of the statement is the isomorphism.
  The comparison map is by definition the homology map of this lift followed by the inverse
  of the injective-resolution identification.

Harris checks surjectivity on `G^{D+1}` differently, from the surjectivity of
`G^D_m(U) ⟶ G^{D+1}_m(U)` and the snake lemma. The Lean proof uses the `Φ`-acyclicity of
`R (D + 1)` instead.

## Provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)* (1999), §2, read in
the original by Worker 26 (checked against the page images).

Printed p.303 = PDF p.5:

> **Fact 2.** There is an integer `D > 0` such that `H^q_c(U, T) = 0` for all `q > D` and any
> étale morphism `U → U(ẽ)`.

Printed p.304 = PDF p.6:

> For any étale sheaf `T` in smooth `ℤ/ℓ^mℤ[S(ẽ)]`-modules over `U(ẽ)`, Berkovich constructs
> an embedding `T ↪ F(T)`, where `F(T)` is again an étale sheaf in smooth
> `ℤ/ℓ^mℤ[S(ẽ)]`-modules over `U(ẽ)`, and which is acyclic for the functor `RΓ_c`:
> `H^q_c(U(ẽ)_F̄, F(T)) = 0` for `q > 0`.

Printed p.305 = PDF p.7:

> It follows from Fact 2 that, for any `m`, the inclusion `τ^{≤q}(F_m^•) → (F_m^•)` is a
> quasi-isomorphism for `q ≥ D`. We let `G_m^• = τ^{≤D+1}(F_m^•)`. It is easy to see that
> truncating in degree `D + 1` rather than `D` guarantees that
>
> **Lemma 2.2 bis.** For each `m` the constant sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic
> resolution of finite length `0 → ℤ/ℓ^mℤ → G_m^0 → G_m^1 → ⋯ → G_m^q → ⋯ → G_m^{D+1} → 0`
> such that, for each `q`, `{G_m^q}` is an `ℓ`-divisible system of `S(ẽ)`-modules over
> `U(ẽ)`.
>
> Indeed, the only point that needs to be checked is the surjectivity of the projection
> `G_m^{D+1}(U) → G_{m-1}^{D+1}(U)` for any `m`, for an étale morphism `U → U(ẽ)_F̄`. But it
> follows from Fact 2 that `G_m^D(U) → G_m^{D+1}(U)` is surjective for all `m`, so the result
> follows from the snake lemma.
>
> Let `d_m^q : G_m^q(U(ẽ)_F̄) → G_m^{q+1}(U(ẽ)_F̄)`, `Z_m^q = ker d_m^q`,
> `B_m^q = im d_m^{q-1}`. Thus Lemma 2.2 provides an isomorphism
>
> (2.3) `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ) ⥲ Z_m^q / B_m^q = H^q(G_m^•(U(ẽ)_F̄))`

This module is derived. It states and proves these steps for an abstract exact coaugmented
functor `F`, an arbitrary `ℓ`-divisible system `T` in place of `ℤ/ℓ^mℤ`, and an abstract
left exact `Φ` in place of `Γ_c(U(ẽ)_F̄, -)`. Harris's `RΓ_c`-acyclicity of `F(T)` and
Fact 2 enter only as the hypotheses `hF` and `hT`, and only for `Φ` itself. Harris states
Fact 2 for every étale `U → U(ẽ)` and uses it for the sections over each such `U`. Here
there is a single functor `Φ`, and the divisible-system property is stated for the section
complexes `Φ(G^•_m)` (`acyclicTruncatedSectionsSystem`), not for the sheaves `G^q`, whose
divisible-system structure is Worker 61's published `truncatedResolutionSystem`.

Not constructed or proved here: Harris's sheaves, the functor `F` and its exactness (Fact 3);
the acyclicity of `F(T)` (Berkovich); Fact 2 itself; the constant system `ℤ/ℓ^mℤ`; the
passage to `H`-invariants after (2.3); and any instance on a twisted or analytic site.

Universes: `C : Type u` with morphisms in `v`, and `E : Type u'` with morphisms in `v'`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`.
