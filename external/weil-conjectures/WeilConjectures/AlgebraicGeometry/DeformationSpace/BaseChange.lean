/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection
public import WeilConjectures.AlgebraicGeometry.RelativeGluing.BaseChange
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeCover

/-!
# Base change of the deformation to the normal cone

Let `h : X' ⟶ X` be a morphism of schemes and `I`, `J` ideal sheaves on `X`, `X'` with
`h^* I ⊆ J`. The maps of extended Rees algebras `Γ(X, U)[t, I t⁻¹] ⟶ Γ(X', U')[t, J t⁻¹]` for
affine opens `U' ⊆ h⁻¹ U` induce a morphism `D_J X' ⟶ D_I X` of deformation spaces, which is a
base change `D_J X' = D_I X ×_{𝔸¹_B} 𝔸¹_{B'}` whenever `h` is a base change of `X ⟶ B` along
`b : B' ⟶ B` and the extended Rees algebras of `J` are base changes of those of `I` on a family of
charts covering `X'`.

We apply this to a morphism `g : V ⟶ B` with a section `s`: the base change
`g' : V' = V ×_B B' ⟶ B'` has the section `s' = (b ≫ s, 𝟙)`, and blueprint `prose-09-12` (5)
states that the deformation space commutes with base change in `B`. For the standard pair this
is `AlgebraicGeometry.Scheme.Hom.isPullback_deformationSpaceMap`.

## Main definitions

- `AlgebraicGeometry.Scheme.polynomialSpecMap`: the morphism `𝔸¹_{X'} ⟶ 𝔸¹_X` over `h`
- `AlgebraicGeometry.Scheme.IdealSheafData.extendedReesPullbackData`:
  the maps of extended Rees algebras
- `AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceMap`: the morphism `D_J X' ⟶ D_I X`

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_deformationSpaceMap_proj`:
  `D_J X' = D_I X ×_{𝔸¹_B} 𝔸¹_{B'}` under the covering hypothesis
- `AlgebraicGeometry.Scheme.Hom.deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection`:
  the comparison `D_{s'} V' ⟶ D_s V` is compatible with the sections `s̃'` and `s̃`
- `AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange_of_cover`:
  blueprint `prose-09-12` (5) under the covering hypothesis
- `AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange_of_isOpenImmersion`:
  blueprint `prose-09-12` (5) for an open immersion `b : B' ⟶ B`
- `AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

open AffineZariskiSite Opposite

variable {X X' : Scheme.{u}} (h : X' ⟶ X)

/-- The maps `h.appLE U U' : Γ(X, U) ⟶ Γ(X', U')` for `U' ⊆ h⁻¹ U` are compatible with the
restriction maps of the small affine Zariski sites. -/
lemma Hom.affineStructurePresheaf_map_appLE {U'₁ U'₂ : X'.AffineZariskiSite}
    {U₁ U₂ : X.AffineZariskiSite} (i' : U'₁ ⟶ U'₂) (i : U₁ ⟶ U₂) (h₁ : U'₁.1 ≤ h ⁻¹ᵁ U₁.1)
    (h₂ : U'₂.1 ≤ h ⁻¹ᵁ U₂.1) :
    X.affineStructurePresheaf.map i.op ≫ h.appLE U₁.1 U'₁.1 h₁ =
      h.appLE U₂.1 U'₂.1 h₂ ≫ X'.affineStructurePresheaf.map i'.op :=
  (h.map_appLE h₁ ((toOpensFunctor X).map i).op).trans
    (h.appLE_map h₂ ((toOpensFunctor X').map i').op).symm

/-- The base change data `Γ(X, U)[t] ⟶ Γ(X', U')[t]` of the relative affine lines along
`h : X' ⟶ X`. -/
@[simps]
noncomputable def polynomialPullbackData :
    PullbackData h X.toPolynomialPresheaf X'.toPolynomialPresheaf where
  map {U' U} hU := CommRingCat.polynomialFunctor.map (h.appLE U.1 U'.1 hU)
  map_naturality i' i h₁ h₂ := by
    have := congr(CommRingCat.polynomialFunctor.map
      $(h.affineStructurePresheaf_map_appLE i' i h₁ h₂))
    rw [Functor.map_comp, Functor.map_comp] at this
    exact this
  app_comp_map hU := (CommRingCat.polynomialC.naturality _).symm

/-- The morphism `𝔸¹_{X'} ⟶ 𝔸¹_X` of relative affine lines over `h : X' ⟶ X`. -/
noncomputable def polynomialSpecMap : X'.polynomialSpec ⟶ X.polynomialSpec :=
  (polynomialPullbackData h).comparison _ _

/-- Under the identifications `Spec_X 𝒪_X[t] ≅ 𝔸¹_X`, the morphism `polynomialSpecMap h` is
`AffineSpace.map h`. -/
@[reassoc]
lemma polynomialSpecMap_polynomialSpecToAffineSpace :
    polynomialSpecMap h ≫ X.polynomialSpecToAffineSpace =
      X'.polynomialSpecToAffineSpace ≫ AffineSpace.map (ULift.{u} (Fin 1)) h := by
  refine hom_ext_of_le_preimage h _ fun U' U hU ↦ AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, Category.assoc, polynomialSpecToAffineSpace_over, polynomialSpecMap,
      PullbackData.comparison_toBase, Category.assoc, Category.assoc, AffineSpace.map_over,
      polynomialSpecToAffineSpace_over_assoc]
  · rw [polynomialSpecMap, PullbackData.ι_comparison_assoc _ _ _ hU,
      ι_polynomialSpecToAffineSpace, ι_polynomialSpecToAffineSpace_assoc, Scheme.Hom.comp_appTop,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply,
      AffineSpace.map_appTop_coord, polynomialSpecChart, polynomialSpecChart,
      AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    exact congrArg (ΓSpecIso _).inv.hom (Polynomial.map_X _)

namespace IdealSheafData

variable {h} in
/-- If `I ≤ h_* J`, that is `h^* I ⊆ J`, then `h` maps the ideal `I(U)` into `J(U')` over affine
opens `U' ⊆ h⁻¹ U`: the chartwise hypothesis of the functoriality of the deformation to the normal
cone (`Scheme.IdealSheafData.deformationSpaceMap`). -/
lemma siteIdeal_map_appLE_le_of_le_map {I : X.IdealSheafData} {J : X'.IdealSheafData}
    (H : I ≤ J.map h) ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄
    (hU : U'.1 ≤ h ⁻¹ᵁ U.1) :
    (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U' := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  have h1 := Hom.ideal_ker_le _ ⟨U.1, U.2⟩ (H ⟨U.1, U.2⟩ ha)
  rw [RingHom.mem_ker] at h1
  rw [Ideal.mem_comap, siteIdeal, ← J.ker_subschemeι, Hom.ker_apply, RingHom.mem_ker,
    Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [Scheme.Hom.app_eq_appLE] at h1
  rw [← Scheme.Hom.appLE_map (J.subschemeι ≫ h) le_rfl
    (homOfLE (J.subschemeι.preimage_mono hU)).op, CommRingCat.comp_apply, h1, map_zero]

variable (I : X.IdealSheafData) (J : X'.IdealSheafData)
  (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
    (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U')

/-- The base change data `Γ(X, U)[t, I t⁻¹] ⟶ Γ(X', U')[t, J t⁻¹]` of the extended Rees
algebras along `h : X' ⟶ X`, for ideal sheaves with `h^* I ⊆ J`. -/
@[simps]
noncomputable def extendedReesPullbackData : PullbackData h I.toReesPresheaf J.toReesPresheaf where
  map {U' U} hU := CommRingCat.ofHom ((I.siteIdeal U).extendedReesAlgebraMap
    (h.appLE U.1 U'.1 hU).hom (J.siteIdeal U') (hJ hU))
  map_naturality i' i h₁ h₂ := by
    ext : 1
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, reesPresheaf_map, reesPresheaf_map]
    simp only [CommRingCat.hom_ofHom]
    rw [Ideal.extendedReesAlgebraMap_comp, Ideal.extendedReesAlgebraMap_comp]
    simp only [← CommRingCat.hom_comp, h.affineStructurePresheaf_map_appLE i' i h₁ h₂]
  app_comp_map hU := by
    ext x
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
    exact Ideal.extendedReesAlgebraMap_algebraMap _ _ (hJ hU) x

/-- The base change data `(Γ(X, U) / I)[t] ⟶ (Γ(X', U') / J)[t]` along `h : X' ⟶ X`, for ideal
sheaves with `h^* I ⊆ J`. -/
@[simps]
noncomputable def quotientPolynomialPullbackData :
    PullbackData h I.toQuotientPolynomialAlgebra J.toQuotientPolynomialAlgebra where
  map {U' U} hU := CommRingCat.polynomialFunctor.map (CommRingCat.ofHom
    (Ideal.quotientMap (J.siteIdeal U') (h.appLE U.1 U'.1 hU).hom
      (Ideal.map_le_iff_le_comap.mp (hJ hU))))
  map_naturality i' i h₁ h₂ := by
    rw [Functor.comp_map, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    have := congr(Ideal.Quotient.mk (J.siteIdeal _)
      ($(h.affineStructurePresheaf_map_appLE i' i h₁ h₂) x))
    simp only [RingHom.comp_apply, CommRingCat.hom_comp, quotientPresheaf_map,
      CommRingCat.hom_ofHom]
    exact this
  app_comp_map hU := by
    ext x
    exact Polynomial.map_C _

lemma polynomialToRees_comp_extendedReesPullbackData_map {U' : X'.AffineZariskiSite}
    {U : X.AffineZariskiSite} (hU : U'.1 ≤ h ⁻¹ᵁ U.1) :
    I.polynomialToRees.app (op U) ≫ (extendedReesPullbackData h I J hJ).map hU =
      (polynomialPullbackData h).map hU ≫ J.polynomialToRees.app (op U') := by
  ext : 1
  exact Ideal.extendedReesAlgebraMap_comp_toExtendedReesAlgebra _ _ (hJ hU)

lemma reesToQuotientPolynomial_comp_quotientPolynomialPullbackData_map
    {U' : X'.AffineZariskiSite} {U : X.AffineZariskiSite} (hU : U'.1 ≤ h ⁻¹ᵁ U.1) :
    I.reesToQuotientPolynomial.app (op U) ≫ (quotientPolynomialPullbackData h I J hJ).map hU =
      (extendedReesPullbackData h I J hJ).map hU ≫ J.reesToQuotientPolynomial.app (op U') := by
  ext : 1
  exact (Ideal.extendedReesAlgebraToPolynomial_comp_extendedReesAlgebraMap
    (h.appLE U.1 U'.1 hU).hom (J.siteIdeal U') (hJ hU) (Ideal.Quotient.mk _) Ideal.mk_ker.ge
    (Ideal.Quotient.mk _) Ideal.mk_ker.ge _
    (Ideal.quotientMap_comp_mk (Ideal.map_le_iff_le_comap.mp (hJ hU)))).symm

lemma polynomialToQuotientPolynomial_comp_quotientPolynomialPullbackData_map
    {U' : X'.AffineZariskiSite} {U : X.AffineZariskiSite} (hU : U'.1 ≤ h ⁻¹ᵁ U.1) :
    I.polynomialToQuotientPolynomial.app (op U) ≫
        (quotientPolynomialPullbackData h I J hJ).map hU =
      (polynomialPullbackData h).map hU ≫ J.polynomialToQuotientPolynomial.app (op U') := by
  rw [Functor.whiskerRight_app, Functor.whiskerRight_app, quotientPolynomialPullbackData_map,
    polynomialPullbackData_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The morphism `D_J X' ⟶ D_I X` of deformation spaces over `h : X' ⟶ X`, for ideal sheaves
with `h^* I ⊆ J`. -/
noncomputable def deformationSpaceMap : J.deformationSpace ⟶ I.deformationSpace :=
  (extendedReesPullbackData h I J hJ).comparison _ _

/-- The morphism `D_J X' ⟶ D_I X` lies over `h : X' ⟶ X`. -/
@[reassoc]
lemma deformationSpaceMap_toBase :
    deformationSpaceMap h I J hJ ≫ I.deformationSpaceProj = J.deformationSpaceProj ≫ h :=
  PullbackData.comparison_toBase _ _ _

/-- The morphism `D_J X' ⟶ D_I X` is compatible with the coordinates `t`. -/
@[reassoc]
lemma deformationSpaceMap_toPolynomialSpec :
    deformationSpaceMap h I J hJ ≫ I.deformationSpaceToPolynomialSpec =
      J.deformationSpaceToPolynomialSpec ≫ polynomialSpecMap h :=
  PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _
    (polynomialToRees_comp_extendedReesPullbackData_map h I J hJ)

/-- The projection `D_I X ⟶ 𝔸¹_X ⟶ 𝔸¹_B ⟶ B` is `D_I X ⟶ X ⟶ B`. -/
lemma deformationSpaceProj_over' {B : Scheme.{u}} (g : X ⟶ B) :
    (I.deformationSpaceToPolynomialSpec ≫ X.polynomialSpecToAffineSpace ≫
      AffineSpace.map (ULift.{u} (Fin 1)) g) ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B =
      (relativeGluingData I.coequifibered_toReesPresheaf).toBase ≫ g := by
  rw [Category.assoc, Category.assoc, AffineSpace.map_over, polynomialSpecToAffineSpace_over_assoc,
    deformationSpaceToPolynomialSpec,
    relativeGluingMap_toBase_assoc _ _ _ I.toPolynomialPresheaf_comp_polynomialToRees]

/-- The morphism `D_J X' ⟶ D_I X` is compatible with the projections to the affine lines
`𝔸¹_{B'} ⟶ 𝔸¹_B`, for `h` lying over `b : B' ⟶ B`. -/
lemma deformationSpaceMap_proj {B B' : Scheme.{u}} (g : X ⟶ B) (g' : X' ⟶ B') (b : B' ⟶ B)
    (w : h ≫ g = g' ≫ b) :
    deformationSpaceMap h I J hJ ≫ I.deformationSpaceToPolynomialSpec ≫
      X.polynomialSpecToAffineSpace ≫ AffineSpace.map (ULift.{u} (Fin 1)) g =
      (J.deformationSpaceToPolynomialSpec ≫ X'.polynomialSpecToAffineSpace ≫
        AffineSpace.map (ULift.{u} (Fin 1)) g') ≫ AffineSpace.map _ b := by
  rw [deformationSpaceMap_toPolynomialSpec_assoc,
    polynomialSpecMap_polynomialSpecToAffineSpace_assoc, ← AffineSpace.map_comp, w,
    AffineSpace.map_comp]
  simp only [Category.assoc]

/-- **Base change of deformation spaces.** If `h : X' ⟶ X` is the base change of `g : X ⟶ B`
along `b : B' ⟶ B` and the extended Rees algebras of `J` are the base changes of those of `I`
on a family of charts covering `X'`, then `D_J X' = D_I X ×_{𝔸¹_B} 𝔸¹_{B'}`. -/
lemma isPullback_deformationSpaceMap_proj
    (hcov : ∀ x : X', ∃ (U' : X'.AffineZariskiSite) (U : X.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1), x ∈ U'.1 ∧ IsPushout (h.appLE U.1 U'.1 hU)
        (I.toReesPresheaf.app (op U)) (J.toReesPresheaf.app (op U'))
        ((extendedReesPullbackData h I J hJ).map hU))
    {B B' : Scheme.{u}} (g : X ⟶ B) (g' : X' ⟶ B') (b : B' ⟶ B) (sq : IsPullback h g' g b) :
    IsPullback (deformationSpaceMap h I J hJ)
      (J.deformationSpaceToPolynomialSpec ≫ X'.polynomialSpecToAffineSpace ≫
        AffineSpace.map (ULift.{u} (Fin 1)) g')
      (I.deformationSpaceToPolynomialSpec ≫ X.polynomialSpecToAffineSpace ≫
        AffineSpace.map (ULift.{u} (Fin 1)) g)
      (AffineSpace.map _ b) := by
  refine IsPullback.of_bot ?_ (deformationSpaceMap_proj h I J hJ g g' b sq.w)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) b)
  rw [deformationSpaceProj_over', deformationSpaceProj_over']
  exact ((extendedReesPullbackData h I J hJ).isPullback_comparison _ _ hcov).paste_vert sq

lemma toPolynomialPresheaf_comp_polynomialToQuotientPolynomial :
    X.toPolynomialPresheaf ≫ I.polynomialToQuotientPolynomial = I.toQuotientPolynomialAlgebra := by
  ext U x
  exact Polynomial.map_C _

/-- The relative affine line `Spec_X (𝒪_X / I)[t]` of `V(I)` is a closed subscheme of the one of
`X`. -/
instance : IsClosedImmersion (relativeGluingMap X.coequifibered_toPolynomialPresheaf
    I.coequifibered_toQuotientPolynomialAlgebra I.polynomialToQuotientPolynomial) :=
  relativeGluingMap_of_forall _ @IsClosedImmersion _ _
    I.toPolynomialPresheaf_comp_polynomialToQuotientPolynomial fun _ ↦
      IsClosedImmersion.spec_of_surjective _
        (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)

/-- The relative affine line `Spec_X (𝒪_X / ⊥)[t]` of the zero ideal is `𝔸¹_X`. -/
instance isIso_relativeGluingMap_polynomialToQuotientPolynomial_bot :
    IsIso (relativeGluingMap X.coequifibered_toPolynomialPresheaf
      (⊥ : X.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra
      (⊥ : X.IdealSheafData).polynomialToQuotientPolynomial) :=
  relativeGluingMap_of_forall _ (MorphismProperty.isomorphisms _) _ _
    (⊥ : X.IdealSheafData).toPolynomialPresheaf_comp_polynomialToQuotientPolynomial fun U ↦ by
      have : IsIso ((⊥ : X.IdealSheafData).polynomialToQuotientPolynomial.app (op U)) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr
          ⟨Polynomial.map_injective _ ((RingHom.injective_iff_ker_eq_bot _).mpr Ideal.mk_ker),
            Polynomial.map_surjective _ Ideal.Quotient.mk_surjective⟩
      exact (inferInstance : IsIso (Spec.map
        ((⊥ : X.IdealSheafData).polynomialToQuotientPolynomial.app (op U))))

/-- Along a closed immersion `h : X' ⟶ X`, the morphism `D_⊥ X' ⟶ D_⊥ X` of deformation spaces of
the zero ideals is a closed immersion: it is the morphism `𝔸¹_{X'} ⟶ 𝔸¹_X` of relative affine
lines. -/
lemma isClosedImmersion_deformationSpaceMap_bot [IsClosedImmersion h]
    (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      ((⊥ : X.IdealSheafData).siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤
        (⊥ : X'.IdealSheafData).siteIdeal U') :
    IsClosedImmersion (deformationSpaceMap h ⊥ ⊥ hJ) := by
  have : IsClosedImmersion (AffineSpace.map (ULift.{u} (Fin 1)) h) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map h).flip ‹_›
  rw [(IsIso.eq_comp_inv _).mpr (deformationSpaceMap_toPolynomialSpec h ⊥ ⊥ hJ),
    (IsIso.eq_comp_inv _).mpr (polynomialSpecMap_polynomialSpecToAffineSpace h)]
  infer_instance

/-- Along any morphism `h : X' ⟶ X`, the deformation space `D_⊥ X' ≅ 𝔸¹_{X'}` of the zero ideal
is the base change of `D_⊥ X ≅ 𝔸¹_X` along `h`:
```
D_⊥ X' ⟶ D_⊥ X
  │         │
  X'   ⟶    X
```
-/
lemma isPullback_deformationSpaceMap_bot
    (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      ((⊥ : X.IdealSheafData).siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤
        (⊥ : X'.IdealSheafData).siteIdeal U') :
    IsPullback (deformationSpaceMap h ⊥ ⊥ hJ) (⊥ : X'.IdealSheafData).deformationSpaceProj
      (⊥ : X.IdealSheafData).deformationSpaceProj h := by
  have e (Y : Scheme.{u}) : (⊥ : Y.IdealSheafData).deformationSpaceProj =
      ((⊥ : Y.IdealSheafData).deformationSpaceToPolynomialSpec ≫ Y.polynomialSpecToAffineSpace) ≫
        𝔸(ULift.{u} (Fin 1); Y) ↘ Y := by
    simpa [AffineSpace.map_id] using (deformationSpaceProj_over' (⊥ : Y.IdealSheafData) (𝟙 Y)).symm
  rw [e X, e X']
  refine IsPullback.paste_vert (IsPullback.of_vert_isIso ⟨?_⟩) (AffineSpace.isPullback_map h)
  rw [deformationSpaceMap_toPolynomialSpec_assoc, Category.assoc,
    polynomialSpecMap_polynomialSpecToAffineSpace]

section OpenImmersion

variable [IsOpenImmersion h]

/-- The image `h(U)` of an affine open `U` under an open immersion. -/
def imageSite (U : X'.AffineZariskiSite) : X.AffineZariskiSite :=
  ⟨h ''ᵁ U.1, U.2.image_of_isOpenImmersion h⟩

lemma map_siteIdeal_imageSite (U : X'.AffineZariskiSite) :
    (I.siteIdeal (imageSite h U)).map (h.appIso U.1).hom.hom = (I.comap h).siteIdeal U := by
  rw [siteIdeal, siteIdeal, ideal_comap_of_isOpenImmersion I h ⟨U.1, U.2⟩]
  exact Ideal.map_comap_of_equiv (h.appIso U.1).commRingCatIsoToRingEquiv

/-- Along an open immersion `h : X' ⟶ X`, the extended Rees algebra of `h^* I` over an affine
open `U` is the base change of the one of `I` over `h(U)`. -/
lemma isPushout_extendedReesPullbackData_imageSite (hJI : J = I.comap h)
    (U : X'.AffineZariskiSite) :
    IsPushout (h.appLE (imageSite h U).1 U.1 (h.preimage_image_eq U.1).ge)
      (I.toReesPresheaf.app (op (imageSite h U))) (J.toReesPresheaf.app (op U))
      ((extendedReesPullbackData h I J hJ).map (h.preimage_image_eq U.1).ge) := by
  subst hJI
  have e : (I.siteIdeal (imageSite h U)).map
      (h.appLE (imageSite h U).1 U.1 (h.preimage_image_eq U.1).ge).hom =
        (I.comap h).siteIdeal U := by
    rw [← map_siteIdeal_imageSite h I U, Scheme.Hom.appIso_hom']
    rfl
  have : IsIso (h.appLE (imageSite h U).1 U.1 (h.preimage_image_eq U.1).ge) := by
    have : IsIso (h.appIso U.1).hom := inferInstance
    rwa [Scheme.Hom.appIso_hom'] at this
  have : IsIso ((extendedReesPullbackData h I (I.comap h) hJ).map (h.preimage_image_eq U.1).ge) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (Ideal.bijective_extendedReesAlgebraMap
      (asIso (h.appLE (imageSite h U).1 U.1 _)).commRingCatIsoToRingEquiv _ e)
  exact IsPushout.of_horiz_isIso ⟨((extendedReesPullbackData h I _ hJ).app_comp_map _).symm⟩

/-- Along an open immersion `h : X' ⟶ X`, the deformation space of `J = h^* I` is the base change
`X' ×_X D_I X` of the deformation space of `I`. -/
lemma isPullback_deformationSpaceMap_of_isOpenImmersion (hJI : J = I.comap h) :
    IsPullback (deformationSpaceMap h I J hJ) J.deformationSpaceProj I.deformationSpaceProj h := by
  refine (extendedReesPullbackData h I J hJ).isPullback_comparison _ _ fun x ↦ ?_
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show x ∈ (⊤ : X'.Opens) from trivial)
  exact ⟨⟨U, hU⟩, _, _, hx, isPushout_extendedReesPullbackData_imageSite _ _ _ _ hJI _⟩

end OpenImmersion

end IdealSheafData

namespace Hom

variable {V B B' : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V) (hs : s ≫ g = 𝟙 B) (b : B' ⟶ B)

/-- The ideal of the base-changed section `s'` contains the pullback of the ideal of `s`, chart by
chart. -/
lemma map_siteIdeal_ker_le_baseChangeSection [IsClosedImmersion s]
    ⦃U' : (pullback g b).AffineZariskiSite⦄ ⦃U : V.AffineZariskiSite⦄
    (hU : U'.1 ≤ pullback.fst g b ⁻¹ᵁ U.1) :
    (s.ker.siteIdeal U).map ((pullback.fst g b).appLE U.1 U'.1 hU).hom ≤
      (baseChangeSection g s hs b).ker.siteIdeal U' := by
  have : IsClosedImmersion (baseChangeSection g s hs b) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeSection g s hs b).flip ‹_›
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hx' := s.ideal_ker_le ⟨U.1, U.2⟩ hx
  rw [RingHom.mem_ker] at hx'
  rw [Ideal.mem_comap, IdealSheafData.siteIdeal, Hom.ker_apply, RingHom.mem_ker,
    Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_congr_hom (baseChangeSection_fst g s hs b), Scheme.Hom.comp_appLE,
    CommRingCat.comp_apply]
  · rw [hx', map_zero]
  · rw [← baseChangeSection_fst g s hs b, Scheme.Hom.comp_preimage]
    exact (baseChangeSection g s hs b).preimage_mono hU

/-- The comparison `𝔸¹_{V(I_{s'})} ⟶ 𝔸¹_{V(I_s)}` is the base change of `𝔸¹_{B'} ⟶ 𝔸¹_B`. -/
@[reassoc]
lemma affineSpaceToQuotientPolynomialSpec_comp_comparison [IsClosedImmersion s] :
    (baseChangeSection g s hs b).affineSpaceToQuotientPolynomialSpec ≫
      (IdealSheafData.quotientPolynomialPullbackData (pullback.fst g b) s.ker
        (baseChangeSection g s hs b).ker
        (map_siteIdeal_ker_le_baseChangeSection g s hs b)).comparison _ _ =
      AffineSpace.map _ b ≫ s.affineSpaceToQuotientPolynomialSpec := by
  rw [← cancel_mono (relativeGluingMap V.coequifibered_toPolynomialPresheaf
    s.ker.coequifibered_toQuotientPolynomialAlgebra s.ker.polynomialToQuotientPolynomial),
    Category.assoc, PullbackData.comparison_comp_relativeGluingMap
      (H := V.coequifibered_toPolynomialPresheaf)
      (H' := (pullback g b).coequifibered_toPolynomialPresheaf) _ _ _ _ _ _
      (IdealSheafData.polynomialToQuotientPolynomial_comp_quotientPolynomialPullbackData_map
        _ _ _ _),
    affineSpaceToQuotientPolynomialSpec_toPolynomialSpec_assoc, Category.assoc,
    affineSpaceToQuotientPolynomialSpec_toPolynomialSpec, ← polynomialSpecMap,
    (IsIso.eq_comp_inv _).mpr (polynomialSpecMap_polynomialSpecToAffineSpace _)]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← AffineSpace.map_comp_assoc,
    baseChangeSection_fst]

/-- The comparison morphism `D_{s'} V' ⟶ D_s V` is compatible with the sections
`s̃' : 𝔸¹_{B'} ⟶ D_{s'} V'` and `s̃ : 𝔸¹_B ⟶ D_s V`. -/
lemma deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection [IsClosedImmersion s] :
    (baseChangeSection g s hs b).deformationSpaceSection ≫
      IdealSheafData.deformationSpaceMap (pullback.fst g b) s.ker
        (baseChangeSection g s hs b).ker (map_siteIdeal_ker_le_baseChangeSection g s hs b) =
      AffineSpace.map _ b ≫ s.deformationSpaceSection := by
  rw [deformationSpaceSection, deformationSpaceSection, Category.assoc,
    IdealSheafData.deformationSpaceMap,
    ← PullbackData.comparison_comp_relativeGluingMap
      (HG := s.ker.coequifibered_toQuotientPolynomialAlgebra) _ _ _ _ _ _ _
      (IdealSheafData.reesToQuotientPolynomial_comp_quotientPolynomialPullbackData_map _ _ _ _),
    affineSpaceToQuotientPolynomialSpec_comp_comparison_assoc]

/-- Blueprint `prose-09-12` (5), assuming that the extended Rees algebras of `s'` are the base
changes of those of `s` on a family of charts covering `V' = V ×_B B'`:
`D_{s'} V' = D_s V ×_{𝔸¹_B} 𝔸¹_{B'}`, compatibly with the sections. -/
theorem exists_isPullback_deformationSpace_baseChange_of_cover [IsClosedImmersion s]
    (hcov : ∀ x : (pullback g b : Scheme.{u}), ∃ (U' : (pullback g b).AffineZariskiSite)
      (U : V.AffineZariskiSite) (hU : U'.1 ≤ pullback.fst g b ⁻¹ᵁ U.1), x ∈ U'.1 ∧
        IsPushout ((pullback.fst g b).appLE U.1 U'.1 hU) (s.ker.toReesPresheaf.app (op U))
          ((baseChangeSection g s hs b).ker.toReesPresheaf.app (op U'))
          ((IdealSheafData.extendedReesPullbackData (pullback.fst g b) s.ker
            (baseChangeSection g s hs b).ker
            (map_siteIdeal_ker_le_baseChangeSection g s hs b)).map hU)) :
    ∃ φ : (baseChangeSection g s hs b).ker.deformationSpace ⟶ s.ker.deformationSpace,
      IsPullback φ (deformationSpaceProj (pullback.snd g b) (baseChangeSection g s hs b))
        (deformationSpaceProj g s) (AffineSpace.map _ b) ∧
      (baseChangeSection g s hs b).deformationSpaceSection ≫ φ =
        AffineSpace.map _ b ≫ s.deformationSpaceSection :=
  ⟨_, IdealSheafData.isPullback_deformationSpaceMap_proj _ _ _ _ hcov g _ b
    (IsPullback.of_hasPullback g b),
    deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection g s hs b⟩


/-- Blueprint `prose-09-12` (5) for a Zariski localization of the base: if `b : B' ⟶ B` is
an open immersion, the deformation space of the base-changed section is the base change of the
deformation space, `D_{s'} V' = D_s V ×_{𝔸¹_B} 𝔸¹_{B'}`. -/
theorem exists_isPullback_deformationSpace_baseChange_of_isOpenImmersion [IsOpenImmersion b]
    [IsClosedImmersion s] :
    ∃ φ : (baseChangeSection g s hs b).ker.deformationSpace ⟶ s.ker.deformationSpace,
      IsPullback φ (deformationSpaceProj (pullback.snd g b) (baseChangeSection g s hs b))
        (deformationSpaceProj g s) (AffineSpace.map _ b) ∧
      φ ≫ s.ker.deformationSpaceProj =
        (baseChangeSection g s hs b).ker.deformationSpaceProj ≫ pullback.fst g b := by
  refine ⟨_, IdealSheafData.isPullback_deformationSpaceMap_proj _ _ _
    (map_siteIdeal_ker_le_baseChangeSection g s hs b) (fun x ↦ ?_) g _ b
    (IsPullback.of_hasPullback g b), IdealSheafData.deformationSpaceMap_toBase _ _ _ _⟩
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (pullback g b).isBasis_affineOpens (show x ∈ (⊤ : (pullback g b).Opens) from trivial)
  exact ⟨⟨U, hU⟩, _, _, hx, IdealSheafData.isPushout_extendedReesPullbackData_imageSite _ _ _ _
    (ker_baseChangeSection g s hs b) _⟩

/-- Blueprint `prose-09-12` (5), base change in `B`: for `g : V ⟶ B` smooth of relative
dimension `d` with a closed section `s`, and any `b : B' ⟶ B`, the deformation space of the
base-changed section `s'` of `g' : V ×_B B' ⟶ B'` is the base change of the deformation space
of `s`,

`D_{s'} V' = D_s V ×_{𝔸¹_B} 𝔸¹_{B'}`,

compatibly with the sections `s̃' = b ×s̃`. For the standard pair this is
`AlgebraicGeometry.Scheme.Hom.isPullback_deformationSpaceMap`. -/
theorem exists_isPullback_deformationSpace_baseChange (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] :
    ∃ φ : (baseChangeSection g s hs b).ker.deformationSpace ⟶ s.ker.deformationSpace,
      IsPullback φ (deformationSpaceProj (pullback.snd g b) (baseChangeSection g s hs b))
        (deformationSpaceProj g s) (AffineSpace.map _ b) ∧
      (baseChangeSection g s hs b).deformationSpaceSection ≫ φ =
        AffineSpace.map _ b ≫ s.deformationSpaceSection := by
  refine exists_isPullback_deformationSpace_baseChange_of_cover g s hs b fun x ↦ ?_
  obtain ⟨U', U, hU, hx, _, H⟩ :=
    exists_isPushout_extendedReesAlgebraMap_baseChange g s hs b d x
  exact ⟨U', U, hU, hx, H⟩

end Hom

end AlgebraicGeometry.Scheme
