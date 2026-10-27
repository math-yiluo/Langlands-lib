# Gluing the invariant spectra of a finite-étale group action

This helper module builds the quotient of a finite étale cover by a finite group over an
arbitrary base scheme `S`. It glues the spectra of invariant sections over the affine opens
of `S`. The module `QuotientCoconeGluingProof` uses it to prove `FiniteGroupQuotientCocones`.
Declarations live in `Langlands.AlgebraicGeometry.FiniteEtale.QuotientGluing`. The module sets
`backward.isDefEq.respectTransparency false`, as `Definitions` does. It contains no statements:
every declaration is a construction or a lemma that this module proves.

Throughout, `D : SingleObj G ⥤ Cover S`, and `coverScheme D` (from the Library module
`AffineQuotientCoconeProof`) is the source of `D.obj (SingleObj.star G)`.

## Invariants commute with principal localization

`isLocalizationAway_fixedPoints` is the algebraic input for gluing. Take rings `R`, `R'`, `A`,
`B` with `[Algebra R A]`, `[Algebra R' B]` and `[Algebra A B]`, a finite group `G` acting on `A`
and `B` (commuting with `R` and `R'`), and `r : R` with
`IsLocalization.Away (algebraMap R A r) B`. Assume the map `A → B` is `G`-equivariant (`hequiv`),
and let `φ` be a ring map from the invariants of `A` to the invariants of `B` that agrees with
`algebraMap A B` on underlying elements (`hφ`). Then, with the algebra structure given by `φ`,
the invariants of `B` are the localization of the invariants of `A` away from the image of `r`.

The proof checks the three conditions of `IsLocalization.Away.mk`.

- The image of `r` is a unit among the invariants. Its inverse in `B` is invariant, because the
  image of `r` is invariant.
- Every invariant `b` has the form `a / rⁿ` with `a` invariant. This is the Library theorem
  `invariantAlgebraLocalization`, which clears numerators. It is applied with `B` viewed as an
  `R`-algebra through `A`, and the needed scalar tower and `SMulCommClass` instances are built
  locally.
- If two invariants agree in `B`, then `rⁿ` times their difference is zero in `A` for some `n`
  (`IsLocalization.Away.exists_of_eq`).

The Library theorem only supplies numerator clearing. The full localization statement for
invariants is proved here.

## The action on sections over the base

- `coverHom D` is the structure morphism of the acted-on cover. `coverMap D g` is the
  automorphism `(D.map (SingleObj.toEnd G g)).hom.left`. `coverMap_comp_coverHom`,
  `coverMap_one` and `coverMap_mul` hold.
- For an open `U` of `S`, `sectionAction D U g` is the ring map
  `(coverMap D g).appLE` on `Γ(coverScheme D, coverHom D ⁻¹ᵁ U)`. Because sections are
  contravariant, `sectionAction_mul` reads
  `sectionAction D U (g * h) = sectionAction D U g ≫ sectionAction D U h`.
  `app_comp_sectionAction` says it fixes the image of `Γ(S, U)`.
- `sectionRes D h` is the restriction between preimages for `V ≤ U`.
  `sectionAction_comp_sectionRes` says restriction commutes with the action.
- `sectionRing D U` is a type synonym (a `def`) for these sections. It carries the
  `Γ(S, U)`-algebra structure from `(coverHom D).app U` and the left action
  `g • a = (sectionAction D U g⁻¹).hom a` (`sectionRing_smul_def`). This is a
  `MulSemiringAction`, and it commutes with `Γ(S, U)`. The convention matches the affine
  proof's `coverRing`.
- `invariantRing D U := FixedPoints.subalgebra Γ(S, U) (sectionRing D U) G`.
  `mem_invariantRing_iff` says membership means every `sectionAction D U g` fixes the element.
  `invariantInclusion D U` is the injective inclusion as a `CommRingCat` morphism, and
  `invariantInclusion_comp_sectionAction` says the action fixes it.

## The invariant presheaf and its gluing

- `invariantRes D h` restricts invariants to invariants. `invariantDiagram D : S.Opensᵒᵖ ⥤ CommRingCat`
  is the presheaf `U ↦ invariantRing D U`.
- `invariantDiagramMap D : S.presheaf ⟶ invariantDiagram D` is the algebra map on each open.
- `coequifibered_invariantDiagramMap` (with `[Finite G]`) proves that its restriction to affine
  opens is coequifibered. By Mathlib's `coequifibered_iff_forall_isLocalizationAway` it is
  enough to check basic opens `D(r) ⊆ U`. The sections over `coverHom D ⁻¹ᵁ D(r)` are the
  localization of those over `coverHom D ⁻¹ᵁ U` away from the image of `r`. This uses
  `Scheme.Hom.preimage_basicOpen` and `isLocalization_basicOpen_of_qcqs`, which applies because
  finite morphisms are quasi-compact and quasi-separated. Restriction is equivariant, so
  `isLocalizationAway_fixedPoints` with `φ = invariantRes` gives the claim.
- `quotientGlueData D` is Mathlib's `Scheme.AffineZariskiSite.relativeGluingData` for this
  coequifibered map. It is a relative gluing datum over the directed cover of `S` by its affine
  opens, with chart `Spec (invariantRing D U)` over each affine open `U`.
- `gluedQuotient D` is the glued scheme, `gluedStructure D : gluedQuotient D ⟶ S` its structure
  morphism, and `gluedCover D` its open cover by the charts.
  - `gluedCover_f` identifies the charts with the colimit inclusions.
  - `gluedCover_f_gluedStructure` shows each chart maps to `S` through
    `Spec.map ((invariantDiagramMap D).app (op U)) ≫ U.fromSpec`.
  - `gluedStructure_preimage` says the preimage of `U` is exactly the range of its chart.
- `gluedStructure_of` shows that a target-local property `P` holds for `gluedStructure D` once it
  holds for `Spec.map ((invariantDiagramMap D).app (op U))` on every affine open `U`. Over each
  affine open, the restriction of `gluedStructure D` is isomorphic to that spectrum map.

## The quotient map

- `gluedMapPiece D U` is defined over the preimage of each affine open `U`. It is the spectrum
  of `invariantInclusion D U` followed by the chart of `U`, precomposed with the canonical map
  from that preimage to the spectrum of its sections. The preimage of an affine open is affine.
- `gluedMapPiece_compat` is the compatibility along inclusions of affine opens. It follows from
  naturality of the colimit inclusions (`colimit.w`).
- `gluedMap D : coverScheme D ⟶ gluedQuotient D` glues these pieces with
  `Scheme.OpenCover.glueMorphismsOfLocallyDirected` over the pullback of the directed cover.
- `ι_gluedMap` and `fromSpec_gluedMap` give the restriction of `gluedMap D` to each preimage:
  `(U.preimage (coverHom D)).fromSpec ≫ gluedMap D = Spec.map (invariantInclusion D U) ≫ (gluedCover D).f U`.
- `coverScheme_hom_ext` shows that maps out of `coverScheme D` agree once they agree after
  every `(U.preimage (coverHom D)).fromSpec`.
- `gluedMap_gluedStructure` gives `gluedMap D ≫ gluedStructure D = coverHom D`.
- `fromSpec_coverMap` gives `fromSpec ≫ coverMap D g = Spec.map (sectionAction D U g) ≫ fromSpec`.
  With `invariantInclusion_comp_sectionAction` this yields invariance: `coverMap_gluedMap` gives
  `coverMap D g ≫ gluedMap D = gluedMap D`.

## Finiteness and étaleness

- For every affine open `U`, `sectionRing_finite` and `sectionRing_etale` show that
  `sectionRing D U` is a finite étale `Γ(S, U)`-algebra. They use `Scheme.Hom.finite_app` and
  `HasRingHomProperty.appLE` for `Etale`.
- Under `[IsLocallyNoetherian S] [Finite G]`, `Γ(S, U)` is noetherian
  (`IsLocallyNoetherian.component_noetherian`). `invariantRing_finite_etale` then applies the
  Library theorem `invariantAlgebraFiniteEtale`.
- The instances `IsFinite (gluedStructure D)` and `Etale (gluedStructure D)` follow from
  `gluedStructure_of`, with `IsFinite.SpecMap_iff` and `HasRingHomProperty.Spec_iff`.

## Imports and provenance

The module imports the Library proofs `AffineQuotientCoconeProof` (for `coverScheme`, and
indirectly `invariantAlgebraFiniteEtale`) and `InvariantAlgebraLocalizationProof`. It also
imports Mathlib's `AlgebraicGeometry.Sites.SmallAffineZariski` and `Tactic.DepRewrite`.

The construction follows SGA 1, Exposé V. The source is `sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.

- Proposition 1.1 and Corollary 1.2 (printed p.88, PDF p.104) treat the affine quotient
  `Spec (A^G)`. The proof of Corollary 1.2 uses the formula `(S⁻¹A)^G = S⁻¹(A^G)` for `S`
  generated by one element `f` of `A^G`. `isLocalizationAway_fixedPoints` is the form of this
  formula used here, with `f` coming from the base.
- Proposition 1.8 (printed p.90, PDF p.106) builds the quotient by gluing the affine quotients
  `Xᵢ/G` of invariant affine opens `Xᵢ`.
- The Corollary 1.8 on the same page says that for `X` affine over `Z`, with `G` acting by
  `Z`-automorphisms, the quotient is defined by the sheaf of invariants `A^G`. This is the
  present situation, with `Z = S` and `Xᵢ` the preimages of the affine opens of `S`.
- Corollary 3.4 (printed p.97, PDF p.113) says the quotient of a finite étale cover is finite
  étale. Here this is reduced to the algebraic Library theorem `invariantAlgebraFiniteEtale`.

The Lean route is internal. It uses Mathlib's relative gluing over the affine Zariski site,
which needs only principal localizations, together with the algebraic lemma above.
