# Sections of ℓ-divisible systems of complexes

Author: Worker 61. Built on the modules
`Langlands.Cohomology.DivisibleSystem.LeftExact` (images of `ℓ`-divisible
systems under left exact functors, and compact sections of smooth sheaves) and
`Langlands.Cohomology.DivisibleSystem.Truncation` (the truncated resolution
systems of Harris's Lemma 2.2 bis), and through them on
`Langlands.Cohomology.DivisibleSystem`, `…DivisibleSystem.Coaugmented` and
`…DivisibleSystem.Resolution`. All names below are in the namespace
`Langlands.Cohomology.DivisibleSystem`. Write `K m` for `K.obj m`, `j` for the
projections `K.projection h : K m ⟶ K m'` (`m' ≤ m`) and `i` for the
inclusions, as in the parent module.

On p.305 Harris passes from the truncated resolutions
`G_m^• = τ_{≤D+1}(F_m^•)` of Lemma 2.2 bis to their sections over
`U(ẽ)_F̄`. He writes `d_m^q : G_m^q(U(ẽ)_F̄) → G_m^{q+1}(U(ẽ)_F̄)`,
`Z_m^q = ker d_m^q`, `B_m^q = im d_m^{q-1}`, and (2.3) identifies
`H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)` with `Z_m^q/B_m^q = H^q(G_m^•(U(ẽ)_F̄))`. After taking
invariants under an open normal pro-`p` subgroup `H ⊂ S(ẽ)`, he says that the
cohomology "is thus canonically calculated by an ℓ-divisible system of
finite-length complexes of `ℤ/ℓ^mℤ[S(ẽ)/H]`-modules, in the obvious sense".
In the proof of Lemma 2.2 bis he checks only the surjectivity of
`G_m^{D+1}(U) → G_{m-1}^{D+1}(U)` for étale `U → U(ẽ)_F̄`.

This module forms the section complexes `{G_m^•(U)}` as one `ℓ`-divisible
system of complexes, for any additive functor `Φ` preserving finite limits in
place of sections. The surjectivity of `Φ` on the projections is an explicit
hypothesis. Acyclicity, the cohomology of the section complexes, the
identification (2.3) and the `H`-invariants are not treated.

## Left exact functors applied degreewise

`C` and `E` are abelian categories, `ℓ : ℕ`,
`K : DivisibleSystem (CochainComplex C ℕ) ℓ` is an `ℓ`-divisible system of
`ℕ`-indexed cochain complexes, and `Φ : C ⥤ E` is additive and preserves finite
limits. The hypothesis `hΦ h q` says that `Φ` maps the degree-`q` component of
the projection `j : K m ⟶ K m'` to an epimorphism, for all `m' ≤ m` and `q`.

- `epi_mapHomologicalComplex_map_projection`: then `Φ` applied degreewise
  (Mathlib's `Φ.mapHomologicalComplex`) maps each projection to an
  epimorphism of complexes. This is Mathlib's
  `HomologicalComplex.epi_of_epi_f`.
- `mapComplexes K Φ hΦ : DivisibleSystem (CochainComplex E ℕ) ℓ` is the
  LeftExact module's `mapLeftExact` along `Φ.mapHomologicalComplex`, which is
  additive and preserves finite limits by Mathlib instances. Its level `m` is
  `Φ` applied to every term and differential of `K m`, and its inclusions and
  projections are `Φ` applied degreewise to those of `K`
  (`mapComplexes_obj`, `mapComplexes_obj_X`, `mapComplexes_obj_d`,
  `mapComplexes_projection_f`, `mapComplexes_inclusion_f`, all by `rfl`).
- `mapComplexes_degree`: the degree-`q` system of `mapComplexes K Φ hΦ` (the
  parent module's `degree`) equals the LeftExact module's `mapLeftExact` of the
  degree-`q` system of `K`. The equality holds by `rfl`.
- `mapComplexesHom K Φ hΦ f hΦ'` is `Φ` applied degreewise to a morphism
  `f : K ⟶ K'` of systems of complexes (the LeftExact module's
  `mapLeftExactHom`). `mapComplexesHom_tower_app_f` gives its components.

## The truncated resolutions

`F : C ⥤ C` is additive and preserves finite limits and finite colimits,
`η : 𝟭 C ⟶ F` has monomorphic components, `T : DivisibleSystem C ℓ` and
`D : ℕ`, as in the Truncation module. Write `F^q` for the term system
`T.termSystem F η q` and `R q` for the residual system
`T.residualSystem F η q`. `Φ : C ⥤ E` is additive and preserves finite
limits. The hypotheses are:

- `hterm q hq h`: for `q ≤ D`, `Φ` maps the projections `j` of `F^q` to
  epimorphisms;
- `hres h`: `Φ` maps the projections `j` of `R (D + 1)` to epimorphisms. For a
  sections functor this is the surjectivity of
  `G_m^{D+1}(U) → G_{m'}^{D+1}(U)` that Harris checks for `m' = m - 1`; the
  LeftExact module's `epi_map_projection_of_succ` shows that consecutive
  levels suffice.

Declarations:

- `epi_map_truncatedResolutionSystem_projection_f`: under `hterm` and `hres`,
  `Φ` maps every degree of every projection of the Truncation module's
  `truncatedResolutionSystem F η T D` to an epimorphism. In degree `q ≤ D` the
  degree-`q` component is the projection of `F^q`, in degree `D + 1` that of
  `R (D + 1)`, and above `D + 1` its target is zero, so its image under the
  additive functor `Φ` has zero target.
- `truncatedResolutionSectionsSystem F η T D Φ hterm hres` is `mapComplexes`
  of the truncated resolution system: the system `{Φ(G_m^•)}`.
  `isZero_truncatedResolutionSectionsSystem_obj_X` says that every level is
  zero in degrees `> D + 1`, so these are finite-length complexes.
- `epi_map_resolutionSystem_projection_f` and
  `resolutionSectionsSystem F η T Φ hall` do the same for the untruncated
  Resolution module's `resolutionSystem F η T`, given the hypothesis `hall`
  for every term system `F^q`.
- `truncatedResolutionSectionsHom F η T D Φ hall hres` is `Φ` applied to the
  inclusion `truncatedResolutionHom` of the Truncation module. The module does
  not say whether it is a quasi-isomorphism; that would need acyclicity.

## Compact sections of the smooth Godement resolutions

`R`, `G`, `X` and `T : SmoothSheafDivisibleSystem R G X ℓ` are as in the smooth
section of the LeftExact module. The exactness of the degree-zero smooth
Godement functor is Worker 3's unproved proposition
`SmoothGodementZeroExactStatement R G X`. Both declarations below take a proof
`h` of it and the hypotheses `hterm`, `hres` as explicit arguments, stated for
the Coaugmented module's `smoothGodementTermSystem h T q` and
`smoothGodementResidualSystem h T (D + 1)`.

- `smoothGodementTruncatedCompactSectionsSystem h T D hterm hres` is
  `truncatedResolutionSectionsSystem` for the smooth Godement functor and the
  compact sections functor `smoothSheafCompactSections R G X` into smooth
  representations `SmoothRep R G`.
- `smoothGodementTruncatedInvariantCompactSectionsSystem h T D hterm hres` is
  the same for the invariant compact sections functor
  `SmoothSheafCohomology.invariantCompactSections R G X` into `ModuleCat R`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.305. Worker 61 read the
page in the scanned original.

1. Systems of section complexes. Harris uses the complexes
   `G_m^•(U(ẽ)_F̄)` and, after `H`-invariants, calls the family "an ℓ-divisible
   system of finite-length complexes [...], in the obvious sense".
   `mapComplexes` gives that sense for any left exact `Φ`: an `ℓ`-divisible
   system in the category of complexes, as in the Resolution module, obtained
   from `K` degree by degree. Left exactness alone does not preserve
   `ℓ`-divisible systems; the epimorphism hypothesis is the condition used by
   the LeftExact module's `mapLeftExact`.
2. Which surjectivity. Harris checks surjectivity on sections only for
   `G^{D+1}`; for the terms `G_m^q = F_m^q`, `q ≤ D`, he treats the
   `ℓ`-divisibility as known from Lemma 2.2. Here both appear as hypotheses
   (`hterm` and `hres`); neither is derived from Fact 2, acyclicity or the
   snake lemma.
3. Sections. The Library's smooth framework is topological. The sections
   functors used are compactly supported sections of smooth equivariant
   sheaves and their invariants under the whole group `G`, as in the
   LeftExact module. They stand in for Harris's sections over `U(ẽ)_F̄`, whose
   cohomology computes `H_c^q` in (2.3). The étale site of `U(ẽ)_F̄` and the
   invariants under a pro-`p` subgroup `H` are not formalized here.
4. Not formalized. The isomorphism (2.3), the cycles and boundaries
   `Z_m^q, B_m^q` as systems, the quasi-isomorphism
   `G_m^•(U(ẽ)_F̄)^H ⊂ G_m^•(U(ẽ)_F̄)`, the free resolutions (2.4)–(2.5) and
   the complexes `C_m^•` of p.306 are not part of this module.

`mapComplexes` and `truncatedResolutionSectionsSystem` are the formal content
of the "obvious sense" for section complexes, with the surjectivity as a
hypothesis. The epimorphism lemmas, the degree and component identifications,
the vanishing above `D + 1`, the morphism and the smooth instances are derived.

## Scope

The module does not prove any surjectivity of projections on sections, any
acyclicity, any statement about the cohomology of the section complexes, or
Harris's (2.3). It does not construct invariants under subgroups other than
`G`, free resolutions, or the complexes `C_m^•`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
