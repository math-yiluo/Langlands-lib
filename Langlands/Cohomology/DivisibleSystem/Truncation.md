# Truncated ℓ-divisible systems of resolutions

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem` (ℓ-divisible systems, Harris 1999,
(2.1)), `Langlands.Cohomology.DivisibleSystem.Coaugmented` (the residual and
term systems of Harris's Lemma 2.2) and
`Langlands.Cohomology.DivisibleSystem.Resolution` (systems of complexes given
degree by degree, and the system of the resolutions of Lemma 2.2). All names
below are in the namespace `Langlands.Cohomology.DivisibleSystem`. Write `T m`
for `T.obj m`.

On p.305 Harris defines, for `q ≥ 0`, the truncation functor on complexes
`τ_{≤q}(C^•)^i = C^i` for `i < q`, `τ_{≤q}(C^•)^q = ker(C^q → C^{q+1})` and
`τ_{≤q}(C^•)^i = 0` for `i > q`. He writes "It follows from Fact 2 that, for
any m, the inclusion `τ_{≤q}(F_m^•) → (F_m^•)` is a quasi-isomorphism for
`q ≥ D`", sets `G_m^• = τ_{≤D+1}(F_m^•)`, and states Lemma 2.2 bis: for each
`m` the constant sheaf `ℤ/ℓ^mℤ` has an `RΓ_c`-acyclic resolution of finite
length `0 → ℤ/ℓ^mℤ → G_m^0 → ⋯ → G_m^{D+1} → 0` such that each `{G_m^q}` is
an `ℓ`-divisible system.

This module builds the truncations `G_m^•` as one `ℓ`-divisible system of
complexes, in the sense of the Resolution module, together with its inclusion
into the system of the resolutions `F_m^•`. It proves that every level is zero
above degree `D + 1` and exact in positive degrees, and that the inclusion is a
quasi-isomorphism of complexes in `C` at every level. It does not prove any
acyclicity, and it does not treat complexes of sections.

## The zero system and morphisms of systems of complexes

`C` is an abelian category and `ℓ : ℕ`.

- `zeroSystem C ℓ` is the `ℓ`-divisible system whose tower is the constant
  functor at the zero object of `C`, with zero inclusions. Every condition holds because the
  middle objects are zero. `isZero_zeroSystem_tower_obj` says each level is
  zero. `fromZeroSystem T` and `toZeroSystem T` are the morphisms of systems
  from and to it.
- `eqToHom_tower_app`: the level-`m` component of the morphism `eqToHom h` of
  systems, for an equality `h : T = T'` of systems, is `eqToHom` of the induced
  equality of level-`m` objects.
- `ofDegreesHom sq sq' f hf : ofDegrees S d sq ⟶ ofDegrees S' d' sq'` is the
  morphism of systems of complexes with degree-`q` components the morphisms of
  systems `f q : S q ⟶ S' q`. The hypothesis `hf` says that the `f q` commute
  with the differentials at every level. Its level-`m` component is the chain
  map `levelHom sq sq' f hf m`, and `ofDegreesHom_tower_app_f` gives its
  degree-`q` component.

## Truncation of a system of complexes given degree by degree

`S : ℕ → DivisibleSystem C ℓ`, `d q : S q ⟶ S (q + 1)` and
`sq q m : (d q).tower.app m ≫ (d (q + 1)).tower.app m = 0` are as in the
Resolution module's `ofDegrees`. `D : ℕ` and `Z : DivisibleSystem C ℓ`, with
morphisms of systems `p : S D ⟶ Z` and `ι : Z ⟶ S (D + 1)`. At every level `m`:
`ι` is a monomorphism (`[∀ m, Mono (ι.tower.app m)]`), `hpι` says that
`p ≫ ι = d D`, and `hιd` says that `ι ≫ d (D + 1) = 0`. The system `Z` plays
the part of Harris's kernel in degree `D + 1`; it need not be the kernel for
the constructions and the statements in degrees `≤ D`.

- `truncationTerm S D Z q` is `S q` for `q ≤ D`, `Z` for `q = D + 1` and
  `zeroSystem C ℓ` for `q > D + 1` (`truncationTerm_of_le`,
  `truncationTerm_of_eq`, `truncationTerm_of_lt`,
  `isZero_truncationTerm_tower_obj`).
- `truncationDifferential S d D Z p q` is `d q` for `q < D`, `p` for `q = D`
  and the morphism to the zero system for `q > D`, each composed with the
  identifications of `truncationTerm_of_le` and `truncationTerm_of_eq`
  (`truncationDifferential_tower_app_of_lt`,
  `truncationDifferential_tower_app_self`).
  `truncationDifferential_comp_tower_app` says that consecutive composites
  vanish at every level. For `q + 1 = D` this uses that `ι` is monic:
  `d (D - 1) ≫ p ≫ ι = d (D - 1) ≫ d D = 0`.
- `truncation S d sq D Z p ι hpι : DivisibleSystem (CochainComplex C ℕ) ℓ` is
  the Resolution module's `ofDegrees` applied to these terms and
  differentials. `truncation_obj_d` gives its level-`m` differentials, and
  `isZero_truncation_obj_X` says that every level is zero in degrees
  `> D + 1`. `truncationDegreeIsoOfLE` and `truncationDegreeIsoTop` identify
  its degree systems (the parent module's `degree`) with `S q` for `q ≤ D` and
  with `Z` in degree `D + 1`.
- `truncationInclusion S D Z ι q : truncationTerm S D Z q ⟶ S q` is the
  identification for `q ≤ D`, `ι` for `q = D + 1` and the morphism from the
  zero system above
  (`truncationInclusion_tower_app_of_le`,
  `truncationInclusion_tower_app_top`). Its level components are isomorphisms
  in degrees `≤ D` (`isIso_truncationInclusion_tower_app`) and monomorphisms in
  every degree (instance `mono_truncationInclusion_tower_app`).
  `truncationInclusion_comm` says that they commute with the differentials;
  in degree `D + 1` this is `hιd`.
- `truncationHom S d sq D Z p ι hpι hιd : truncation … ⟶ ofDegrees S d sq` is
  the morphism of systems of complexes with these components
  (`ofDegreesHom`). `truncationHom_tower_app_f` gives its components, and its
  level components are monomorphisms of complexes
  (instance `mono_truncationHom_tower_app`).

Homology statements, at every level `m`:

- `truncationHom_quasiIsoAt_of_le`: the level-`m` component of
  `truncationHom` is a quasi-isomorphism in every degree `q ≤ D`. The previous
  degree (`q - 1`, or `0` if `q = 0`) and `q` are at most `D`, where the
  components are isomorphisms, and in degree `q + 1` the component is a
  monomorphism, so Mathlib's
  `ShortComplex.quasiIso_of_epi_of_isIso_of_mono` applies.
- `truncation_obj_exactAt_top`: if `p` is an epimorphism at every level, every
  level of the truncation is exact in degree `D + 1`. Degree `D + 2` is zero,
  so exactness says that the differential from degree `D` is an epimorphism.
- `truncation_obj_exactAt_of_lt`: every level is exact in degrees `> D + 1`,
  where it is zero.
- `truncationHom_quasiIso`: if `p` is an epimorphism at every level and the
  level-`m` complex of `ofDegrees S d sq` is exact in every degree `≥ D + 1`,
  the level-`m` component of `truncationHom` is a quasi-isomorphism. In
  degrees `≥ D + 1` both complexes are exact.

Under the hypotheses of `truncationHom_quasiIso`, `ι` identifies `Z m` with
the kernel of `d (D + 1)` at level `m`, but the module does not state this. For the
resolutions it is the LeftExact module's `residualInclusionIsKernel`, see
below.

## The truncated resolutions of Lemma 2.2 bis

`F : C ⥤ C` is additive and preserves finite limits and finite colimits,
`η : 𝟭 C ⟶ F` has monomorphic components, `T : DivisibleSystem C ℓ` and
`D : ℕ`, as in the Resolution module. Write `F^q` for the term system
`T.termSystem F η q`, `R q` for the residual system `T.residualSystem F η q`
and `d^q` for `T.termDifferential F η q`.

- `truncatedResolutionSystem F η T D` is `truncation` with `S q = F^q`,
  `d q = d^q`, `Z = R (D + 1)`, `p` the residual quotient
  `T.residualQuotient F η D : F^D ⟶ R (D + 1)` and `ι` the residual inclusion
  `T.residualInclusion F η (D + 1) : R (D + 1) ⟶ F^{D+1}`. The hypotheses hold
  by the Coaugmented module: `d^D` is by definition the residual quotient
  followed by the residual inclusion (`termDifferential_tower_app`), the
  residual inclusion is monic and has zero composite with `d^{D+1}`
  (`residualInclusion_termDifferential_tower_app`).
- `truncatedResolutionHom F η T D` is the inclusion `truncationHom` into
  `T.resolutionSystem F η`.
- `isZero_truncatedResolutionSystem_obj_X`: every level is zero in degrees
  `> D + 1`.
- Instance `truncatedResolutionHom_quasiIso`: at every level `m` the inclusion
  is a quasi-isomorphism. The residual quotient is an epimorphism at every
  level, and the Resolution module's `resolutionSystem_obj_exactAt` gives
  exactness of the resolution in positive degrees.
- `truncatedResolutionSystem_obj_exactAt`: every level of the truncated system
  is exact in degree `q + 1` for every `q`, by Mathlib's
  `exactAt_iff_of_quasiIsoAt`.

The degree-`(D + 1)` term is Harris's kernel: the Coaugmented module's
`residualInclusion_termDifferential_exact` says that
`R (D + 1) m ⟶ F^{D+1} m ⟶ F^{D+2} m` is exact, and the residual inclusion is
monic, so it is a kernel of `d^{D+1}` at level `m`. The module
`Langlands.Cohomology.DivisibleSystem.LeftExact` (accepted for the Library, not
imported here) states this as `residualInclusionIsKernel`.

The degree-zero term is `F^0` because `0 ≤ D`. As in the Resolution module, the
augmentation `T m ⟶ F^0 m` is not part of the complexes, and exactness in
degree 0 of the augmented complex is not stated here.

## The smooth Godement functor

`R`, `G`, `X` and `T : SmoothSheafDivisibleSystem R G X ℓ` are as in the smooth
section of the Resolution module. The exactness of the degree-zero smooth
Godement functor is Worker 3's unproved proposition
`SmoothGodementZeroExactStatement R G X`, and the declarations below take a
proof `h` of it as an explicit argument.

- `smoothGodementTruncatedResolutionSystem h T D` is
  `truncatedResolutionSystem` for `smoothZeroFunctor R G X` and
  `smoothCoaugmentation R G X`: an `ℓ`-divisible system of cochain complexes of
  smooth equivariant sheaves, zero above degree `D + 1`.
- `smoothGodementTruncatedResolutionHom h T D` is its inclusion into the
  Resolution module's `smoothGodementResolutionSystem h T`, and
  `smoothGodementTruncatedResolutionHom_quasiIso` says that it is a
  quasi-isomorphism at every level.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.305 (Fact 2 on p.303).
Worker 61 read the pages in the scanned original.

1. Truncation. Harris's `τ_{≤D+1}` keeps the terms in degrees `≤ D`, puts the
   kernel of `C^{D+1} → C^{D+2}` in degree `D + 1` and zero above. The generic
   `truncation` takes the degree-`(D + 1)` term as data `Z`, with `p` and `ι`,
   because systems of complexes are built degree by degree here and the
   Library has no kernel system of a morphism of `ℓ`-divisible systems. For the
   resolutions, `Z = R (D + 1)` is Harris's kernel at every level, as explained
   above. Mathlib's `CochainComplex.truncLE` is for `ℤ`-indexed complexes; the
   complexes here are indexed by `ℕ`, as in the Resolution module.
2. ℓ-divisibility of the `G^q`. Lemma 2.2 bis says that each `{G_m^q}` is an
   `ℓ`-divisible system. Here the degree systems are `F^q` for `q ≤ D`,
   `R (D + 1)` and the zero system, which are `ℓ`-divisible systems in `C` by
   the Coaugmented module and `zeroSystem`. Harris's check of the surjectivity
   of `G_m^{D+1}(U) → G_{m-1}^{D+1}(U)` for étale `U → U(ẽ)_F̄`, deduced from
   Fact 2 and the snake lemma, concerns sections. It is not needed for systems
   in `C` and is not formalized here; the LeftExact module takes such
   surjectivity as a hypothesis.
3. Quasi-isomorphism. The module proves that `G_m^• → F_m^•` is a
   quasi-isomorphism of complexes in `C`, for every `D`. In `C` this only uses
   that `F_m^•` is exact in positive degrees. Harris's statement that the
   inclusion is a quasi-isomorphism "for `q ≥ D`" and that this "follows from
   Fact 2" concerns sections: Fact 2 (p.303) gives an integer `D > 0` with
   `H_c^q(U, T) = 0` for all `q > D` and every étale `U → U(ẽ)`, which makes
   the truncation harmless after taking compactly supported sections over such
   `U`. That statement, and the `RΓ_c`-acyclicity of the `G_m^q` in Lemma
   2.2 bis, are not formalized.
4. Hypotheses and general `T`. As in the Coaugmented and Resolution modules,
   the exactness of `F` (Harris's Fact 3) is a hypothesis, the construction
   takes any `ℓ`-divisible system `T` and any `D`, and the constant sheaves
   `ℤ/ℓ^mℤ` are not constructed. Harris's `D` is the bound of Fact 2; here
   `D` is arbitrary.

`truncation` and `truncatedResolutionSystem` are the formal content of
Harris's `G_m^• = τ_{≤D+1}(F_m^•)` as one `ℓ`-divisible system of complexes.
The zero system, the morphisms between systems of complexes, the inclusion,
the exactness and quasi-isomorphism statements and the smooth instance are
derived.

## Scope

The module does not prove Harris's Facts 2 and 3, any acyclicity, the
surjectivity of any projection on sections, or any statement about complexes
of sections or compactly supported cohomology. It does not construct the
constant systems `ℤ/ℓ^mℤ`, the free resolutions and the complexes `C_m^•` of
pp.305–306, and it does not state the kernel property of the degree-`(D + 1)`
term for the generic truncation.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
