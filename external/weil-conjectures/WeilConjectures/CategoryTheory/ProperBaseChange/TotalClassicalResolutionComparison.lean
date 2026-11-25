/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Total and classical right-derived comparisons on a supplied resolution

Source: Stacks Project, Derived Categories, Tags 015E and 070K; the total/plus
compatibility and the injective-resolution construction of classical derived functors.
(blueprint: lem-weil-pbc-total-classical-resolution-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
noncomputable section

private theorem inverse_comparison
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {Z : D} (a : F.obj A ⟶ Z) [IsIso a] (b : A ⟶ B) [IsIso b]
    (t : Z ⟶ F.obj B) (h : a ≫ t = F.map b) :
    t ≫ F.map (inv b) = inv a := by
  apply (cancel_epi a).1
  rw [← Category.assoc, h, ← F.map_comp, IsIso.hom_inv_id, F.map_id, IsIso.hom_inv_id]

private theorem factorization_cancel
    {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (e : E ≅ D) {t : A ⟶ E}
    (h : t = a ≫ b ≫ e.inv) : t ≫ e.hom = a ≫ b := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem total_plus_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (L : HomotopyCategory.Plus C) :
    F.rightDerivedFunctorUnit.app L.obj ≫
        (F.rightDerivedFunctorPlusCompatibility.app (DerivedCategory.Plus.Qh.obj L)).inv =
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app L) := by
  apply (Iso.comp_inv_eq _).2
  have h := (Functor.rightDerivedNatTrans_app
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
    F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
    (HomotopyCategory.Plus.quasiIso C) (𝟙 _) L).symm
  simp only [NatTrans.id_app, Category.id_comp] at h
  change F.rightDerivedFunctorUnit.app L.obj =
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app L) ≫
      (F.rightDerivedFunctorPlusCompatibility.app
        (DerivedCategory.Plus.Qh.obj L)).hom at h
  exact h

private theorem total_classical_chosen
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (M : C) (n : ℕ) :
    letI := CochainComplex.isKInjective_of_injective (injectiveResolution M).cochainComplex 0
    (F.homologyRightDerivedFunctorObjSingleFunctorIso M n).hom =
      (DerivedCategory.homologyFunctor D (n : ℤ)).map
        (F.rightDerivedFunctor.map
          (((DerivedCategory.singleFunctorIsoCompQ C 0).app M).hom ≫
            DerivedCategory.Q.map (injectiveResolution M).ι') ≫
          (F.rightDerivedFunctorObjQIso (injectiveResolution M).cochainComplex).hom) ≫
        ((DerivedCategory.homologyFunctorFactors D (n : ℤ)).app _).hom ≫
        ((injectiveResolution M).isoRightDerivedObjCochainComplex F n).inv := by
  let := CochainComplex.isKInjective_of_injective (injectiveResolution M).cochainComplex 0
  let R := injectiveResolution M
  let L : CochainComplex.Plus C := ⟨R.cochainComplex, 0, inferInstance⟩
  let H := DerivedCategory.homologyFunctor D (n : ℤ)
  have hu := total_plus_unit F ((HomotopyCategory.Plus.quotient C).obj L)
  let e := (DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
    asIso (DerivedCategory.Q.map R.ι')
  let t := (DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
    asIso (DerivedCategory.Q.map R.ι') ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app R.cochainComplex
  let v := DerivedCategory.Plus.ι.preimageIso
    (X := (DerivedCategory.Plus.singleFunctor C 0).obj M)
    (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj L)) t
  let ηp := F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L)
  let η := F.rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cochainComplex)
  have hp : (F.rightDerivedFunctorPlusCompatibility.app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj L))).inv ≫
      DerivedCategory.Plus.ι.map (inv ηp) = inv η := by
    exact inverse_comparison DerivedCategory.Plus.ι η ηp _ hu
  have hn := F.rightDerivedFunctorPlusCompatibility.inv.naturality v.hom
  dsimp only [Functor.comp_map] at hn
  have ht : DerivedCategory.Plus.ι.map v.hom = t.hom := by
    dsimp only [v]
    erw [Functor.preimageIso_hom, Functor.map_preimage]
  have hm : (F.rightDerivedFunctorPlusCompatibility.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj M)).inv ≫
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlus.map v.hom ≫ inv ηp) =
      F.rightDerivedFunctor.map e.hom ≫
        F.rightDerivedFunctor.map
          ((DerivedCategory.quotientCompQhIso C).inv.app R.cochainComplex) ≫ inv η := by
    erw [DerivedCategory.Plus.ι.map_comp, ← Category.assoc, ← hn, ht]
    erw [Category.assoc, hp]
    have ht' : t.hom = e.hom ≫
        (DerivedCategory.quotientCompQhIso C).inv.app R.cochainComplex := by
      dsimp only [t, e, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
      exact (Category.assoc _ _ _).symm
    rw [ht']
    exact F.rightDerivedFunctor.map_comp_assoc _ _ _
  let qC := (DerivedCategory.Plus.quotientCompQhIso C).app L
  let qD := (DerivedCategory.Plus.quotientCompQhIso D).app (F.rightDerivedPlusComplex M)
  let v' := DerivedCategory.Plus.ι.preimageIso
    (X := (DerivedCategory.Plus.singleFunctor C 0).obj M)
    (Y := DerivedCategory.Plus.Q.obj L) e
  have hUnit : F.rightDerivedFunctorPlusUnit.app L =
      qD.inv ≫ ηp ≫ F.rightDerivedFunctorPlus.map qC.hom := by
    have h1 : F.rightDerivedFunctorPlusUnit.app L =
        (DerivedCategory.Plus.quotientCompQhIso D).inv.app (F.mapCochainComplexPlus.obj L) ≫
          DerivedCategory.Plus.Qh.map (F.quotientCompMapHomotopyCategoryPlusIso.inv.app L) ≫
            ηp ≫ F.rightDerivedFunctorPlus.map qC.hom :=
      F.rightDerivedFunctorPlusUnit_app L
    have h2 : DerivedCategory.Plus.Qh.map
        (F.quotientCompMapHomotopyCategoryPlusIso.inv.app L) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    rw [h1, h2]
    exact congrArg (_ ≫ ·) (Category.id_comp _)
  have hv : v.hom ≫ qC.hom = v'.hom := by
    apply DerivedCategory.Plus.ι.map_injective
    rw [Functor.map_comp]
    dsimp only [v, v']
    erw [Functor.preimageIso_hom, Functor.map_preimage, Functor.preimageIso_hom,
      Functor.map_preimage]
    dsimp only [t, e, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hplus : (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ M).hom =
      F.rightDerivedFunctorPlus.map v.hom ≫ inv ηp ≫ qD.hom := by
    rw [← cancel_mono (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ M).inv, Iso.hom_inv_id]
    dsimp only [Functor.rightDerivedFunctorPlusObjSingleFunctorIsoQ, Iso.trans_inv,
      Iso.symm_inv, asIso_hom, Functor.mapIso_inv]
    erw [hUnit]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc,
      ← Functor.map_comp]
    erw [reassoc_of% hv]
    rw [Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  have hqD : DerivedCategory.Plus.ι.map qD.hom =
      (DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex) := rfl
  let c := (F.rightDerivedFunctorPlusCompatibility.app
    ((DerivedCategory.Plus.singleFunctor C 0).obj M)).inv
  let b := DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlus.map v.hom ≫ inv ηp)
  let j := (DerivedCategory.Plus.homologyFunctorObjQIso
    (F.rightDerivedPlusComplex M) (n : ℤ)).hom
  let k := (R.isoRightDerivedObjCochainComplex F n).inv
  calc
    _ = H.map (c ≫ b ≫ DerivedCategory.Plus.ι.map qD.hom) ≫ j ≫ k := by
      dsimp only [Functor.homologyRightDerivedFunctorObjSingleFunctorIso,
        Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso,
        Iso.trans, Iso.symm, Functor.mapIso, Iso.app]
      erw [hplus]
      dsimp only [DerivedCategory.Plus.homologyFunctor, Functor.comp_map, b]
      rw [← Category.assoc (F.rightDerivedFunctorPlus.map v.hom), Functor.map_comp]
      exact (H.map_comp_assoc c _ (j ≫ k)).symm
    _ = H.map ((F.rightDerivedFunctor.map e.hom ≫
        F.rightDerivedFunctor.map
          ((DerivedCategory.quotientCompQhIso C).inv.app R.cochainComplex) ≫ inv η) ≫
          DerivedCategory.Plus.ι.map qD.hom) ≫ j ≫ k := by
      rw [← hm, Category.assoc]
    _ = _ := by
      rw [hqD]
      dsimp only [j, DerivedCategory.Plus.homologyFunctorObjQIso,
        Functor.rightDerivedFunctorObjQIso, e, Iso.trans_hom,
        Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, asIso_inv]
      simp only [Functor.map_comp, Category.assoc]
      rfl

private theorem total_model_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (a : I ⟶ J) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map a) ≫
        (F.rightDerivedFunctorObjQIso J).hom =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a) := by
  let R := F.rightDerivedFunctor
  let η := F.rightDerivedFunctorUnit
  let π := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have sq₁ : CommSq (DerivedCategory.Q.map a)
      ((DerivedCategory.quotientCompQhIso C).inv.app I)
      ((DerivedCategory.quotientCompQhIso C).inv.app J)
      (DerivedCategory.Qh.map (π.map a)) :=
    ⟨DerivedCategory.quotientCompQhIso_inv_naturality a⟩
  have su : CommSq (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (π.map a)))
      (asIso (η.app (π.obj I))).hom (asIso (η.app (π.obj J))).hom
      (R.map (DerivedCategory.Qh.map (π.map a))) := ⟨η.naturality (π.map a)⟩
  have sq₃ : CommSq (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (π.map a)))
      ((DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
      ((DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)) :=
    ⟨DerivedCategory.quotientCompQhIso_hom_naturality
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)⟩
  have hh := (((sq₁.map R).vert_comp su.vert_inv).vert_comp sq₃).w
  dsimp only [R, η, π] at hh
  dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans, Iso.symm,
    Functor.mapIso, Iso.app]
  simpa only [Category.assoc] using hh

/-- The canonical total/classical cohomology comparison computed on any supplied
injective resolution, retaining the actual augmentation and both localization factors.
Source: Stacks Project, Derived Categories, Tags 015E and 070K; total/plus compatibility.
(blueprint: lem-weil-pbc-total-classical-resolution-comparison).

Proof: For the chosen injective resolution, expand the total/classical comparison into
its total/plus compatibility and the bounded-below single-object comparison. The
uniqueness equation for rightDerivedFunctorPlusCompatibility identifies its composite
with the total derived unit with the image of the plus derived unit. Naturality moves
this comparison past the localized augmentation. On the resolution both units are
invertible, so their inverses give rightDerivedFunctorObjQIso. The homotopy and derived
homology factorizations compose to homologyFunctorFactors. This proves the formula for
the chosen resolution. For any other resolution I, choose an augmentation-preserving
comparison from the chosen one to I. Naturality of the total derived unit and the
localization/homology comparison identifies the two total computations. Naturality of
isoRightDerivedObjCochainComplex identifies the two classical computations. The
comparison induces the identity on the resolved coefficient, so the right-derived
identity cancels and gives the displayed formula for I. No exactness of F is needed;
the same construction applies to n = 0, zero objects and the zero functor. -/
theorem CategoryTheory.Functor.totalClassicalResolutionComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (M : C) (I : InjectiveResolution M) (n : ℕ) :
    letI := CochainComplex.isKInjective_of_injective I.cochainComplex 0
    (F.homologyRightDerivedFunctorObjSingleFunctorIso M n).hom =
      (DerivedCategory.homologyFunctor D (n : ℤ)).map
        (F.rightDerivedFunctor.map
          (((DerivedCategory.singleFunctorIsoCompQ C 0).app M).hom ≫
            DerivedCategory.Q.map I.ι') ≫
          (F.rightDerivedFunctorObjQIso I.cochainComplex).hom) ≫
        ((DerivedCategory.homologyFunctorFactors D (n : ℤ)).app _).hom ≫
        (I.isoRightDerivedObjCochainComplex F n).inv := by
  let := CochainComplex.isKInjective_of_injective I.cochainComplex 0
  let R := injectiveResolution M
  let := CochainComplex.isKInjective_of_injective R.cochainComplex 0
  let φ : R.Hom I (𝟙 M) :=
    ⟨InjectiveResolution.desc (𝟙 M) I R, by
      simp only [InjectiveResolution.desc_commutes_zero, Functor.map_id,
        HomologicalComplex.id_f, Category.id_comp]⟩
  let e₀ := (DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
    asIso (DerivedCategory.Q.map R.ι')
  let e := (DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
    asIso (DerivedCategory.Q.map I.ι')
  let H := DerivedCategory.homologyFunctor D (n : ℤ)
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let m₀ := H.map (F.rightDerivedFunctor.map e₀.hom ≫
    (F.rightDerivedFunctorObjQIso R.cochainComplex).hom) ≫
      (DerivedCategory.homologyFunctorFactors D (n : ℤ)).hom.app (G.obj R.cochainComplex)
  let m := H.map (F.rightDerivedFunctor.map e.hom ≫
    (F.rightDerivedFunctorObjQIso I.cochainComplex).hom) ≫
      (DerivedCategory.homologyFunctorFactors D (n : ℤ)).hom.app (G.obj I.cochainComplex)
  have haug : e₀.hom ≫ DerivedCategory.Q.map φ.hom' = e.hom := by
    dsimp only [e₀, e, Iso.trans_hom, asIso_hom]
    erw [Category.assoc, ← DerivedCategory.Q.map_comp, φ.ι'_comp_hom']
    simp only [Functor.map_id, Category.id_comp]
  have s₀ : CommSq (𝟙 ((DerivedCategory.singleFunctor C 0).obj M))
      e₀.hom e.hom (DerivedCategory.Q.map φ.hom') :=
    ⟨by simpa only [Category.id_comp] using haug.symm⟩
  have s₁ : CommSq (F.rightDerivedFunctor.map (DerivedCategory.Q.map φ.hom'))
      (F.rightDerivedFunctorObjQIso R.cochainComplex).hom
      (F.rightDerivedFunctorObjQIso I.cochainComplex).hom
      (DerivedCategory.Q.map (G.map φ.hom')) := ⟨total_model_naturality F φ.hom'⟩
  have s₂ : CommSq (H.map (DerivedCategory.Q.map (G.map φ.hom')))
      ((DerivedCategory.homologyFunctorFactors D (n : ℤ)).hom.app (G.obj R.cochainComplex))
      ((DerivedCategory.homologyFunctorFactors D (n : ℤ)).hom.app (G.obj I.cochainComplex))
      (HomologicalComplex.homologyMap (G.map φ.hom') (n : ℤ)) :=
    ⟨(DerivedCategory.homologyFunctorFactors D (n : ℤ)).hom.naturality (G.map φ.hom')⟩
  have hm : m₀ ≫ HomologicalComplex.homologyMap (G.map φ.hom') (n : ℤ) = m := by
    have hh := ((((s₀.map F.rightDerivedFunctor).vert_comp s₁).map H).vert_comp s₂).w
    simpa only [Functor.map_id, Category.id_comp] using hh.symm
  have hi : HomologicalComplex.homologyMap (G.map φ.hom') (n : ℤ) ≫
      (I.isoRightDerivedObjCochainComplex F n).inv =
      (R.isoRightDerivedObjCochainComplex F n).inv := by
    simpa only [Functor.map_id, Category.comp_id] using
      R.isoRightDerivedObjCochainComplex_inv_naturality φ F n
  calc
    _ = m₀ ≫ (R.isoRightDerivedObjCochainComplex F n).inv := by
      simpa only [m₀, H, G, R, e₀, Iso.trans_hom, asIso_hom, Iso.app_hom,
        Category.assoc] using
        total_classical_chosen F M n
    _ = m₀ ≫ HomologicalComplex.homologyMap (G.map φ.hom') (n : ℤ) ≫
        (I.isoRightDerivedObjCochainComplex F n).inv := congrArg (m₀ ≫ ·) hi.symm
    _ = m ≫ (I.isoRightDerivedObjCochainComplex F n).inv := by
      rw [← Category.assoc, hm]
    _ = _ := by
      dsimp only [m, H, G, e, Iso.trans_hom, asIso_hom, Iso.app_hom]
      rw [Category.assoc]
