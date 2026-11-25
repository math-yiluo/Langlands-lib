/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsComplexUnit
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.MixedPullbackSectionsCounitUnit
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-! # The target affine model and its pullback unit normalization
Source: Stacks Project, Tags 06Z0, 08DW(2) and 0D5T.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance 2000] Functor.preservesZeroMorphisms_of_additive

private theorem cancel_right_iso
    {B : Type*} [Category B] {X Y Z W : B}
    (a : X ⟶ Y) (b : X ⟶ Z) (c : Z ⟶ W) (s : W ⟶ Y) [IsIso s]
    (h : a = b ≫ c ≫ s) : a ≫ inv s = b ≫ c := by
  rw [h, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem isIso_leftDerivedCounit_of_isIso
    {A B D : Type*} [Category A] [Category B] [Category D]
    {q : A ⥤ B} {F : A ⥤ D} {L : B ⥤ D}
    (W : MorphismProperty A) [q.IsLocalization W]
    (ε₀ ε : q ⋙ L ⟶ F) [L.IsLeftDerivedFunctor ε₀ W]
    [L.IsLeftDerivedFunctor ε W] (X : A) [IsIso (ε₀.app X)] :
    IsIso (ε.app X) := by
  let e := Functor.leftDerivedUnique L L ε₀ ε W
  have he : e.hom.app (q.obj X) ≫ ε.app X = ε₀.app X := by
    simpa only [e, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
      Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app L L ε₀ ε W (𝟙 _) X
  have hh : ε.app X = e.inv.app (q.obj X) ≫ ε₀.app X := by
    rw [← he]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [hh]
  infer_instance

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

private theorem mixedPullbackCounit_isIso {S T : Scheme.{u}} (g : T ⟶ S)
    [(Scheme.Modules.tensorPullback g).Additive]
    (C : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (ε : DerivedCategory.Qh ⋙ derivedPullback.{u, w} g ⟶
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings T.toRingedSpace)))
    [(derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (.up ℤ))]
    (hC : CochainComplex.IsKFlatTensor (R := S.sheaf) C) :
    IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) := by
  classical
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let K := Scheme.Modules.tensorPullback g
  let q := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε₀, hL, htri, hflat⟩ :=
      (derivedPullback_spec.{u, w} g)
  have hEq : E = K := CategoryTheory.Functor.ext hE (fun _ _ a ↦ hEmap a)
  subst E
  have : IsIso (ε₀.app (q.obj C)) := hflat C hC
  have : (derivedPullback g).IsLeftDerivedFunctor ε₀
      (HomotopyCategory.quasiIso A (.up ℤ)) := hL
  exact
    isIso_leftDerivedCounit_of_isIso (L := derivedPullback g)
      (HomotopyCategory.quasiIso A (.up ℤ)) ε₀ ε (q.obj C)

variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

private theorem mixedSectionsComplexUnit_isIso_of_iso (X : Scheme.{u})
    {C D : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (i : C ≅ D) [IsIso (mixedSectionsComplexUnit X D)] :
    IsIso (mixedSectionsComplexUnit X C) := by
  let H := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  let s : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ schemeDerivedGlobalSections X :=
    Functor.whiskerLeft (H.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso _).inv ≫
      Functor.whiskerRight (H.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
      Functor.whiskerLeft q H.rightDerivedFunctorUnit ≫
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).hom
        (schemeDerivedGlobalSections X)
  have hn := s.naturality i.hom
  change DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map i.hom) ≫
      mixedSectionsComplexUnit X D =
    mixedSectionsComplexUnit X C ≫
      (schemeDerivedGlobalSections X).map (DerivedCategory.Q.map i.hom) at hn
  have he : mixedSectionsComplexUnit X C =
      DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map i.hom) ≫
        mixedSectionsComplexUnit X D ≫
          (schemeDerivedGlobalSections X).map (DerivedCategory.Q.map i.inv) := by
    rw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, i.hom_inv_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [he]
  infer_instance

-- The affine chart and localization factors require larger definitional-equality searches.
/-- The pullback counit and affine sections comparison normalize the target unit.
Source: Stacks Project, Tags 06Z0, 08DW(2), 0D5T.
(blueprint: lem-sc-mixed-affine-pullback-unit-normalization).

Proof: Tilde preserves K-flatness, and exact restriction through the spectrum chart
preserves it, so C=F(P) is K-flat. Its derived pullback counit is invertible.
Termwise tensor-pullback/tilde base change and toSpecΓ naturality identify K(C)
with the affine chart complex of E(P) on T. The affine derived sections comparison
is thus invertible on K(C), with no boundedness restriction. Define b by taking
sections of the pullback counit and then the inverse of that sections comparison.
The pinned derived pullback adjunction unit factors through the counit by
exists_schemeDerivedAdjunction and derivedη_fac_app. Apply sections, move its unit
past the ordinary pullback unit by naturality, and substitute the normalized
mixedGlobalSectionsDirectImageIso derived-unit equation. Naturality of that Leray
isomorphism at the counit produces the displayed equality. Insert the complex to
homotopy quotient factor isomorphisms and the exact scalar restriction factor at
both endpoints. This statement uses neither scalar extension nor any comparison c
or hc; it computes only the pullback side. Empty schemes and P=0 are covered by
the same naturality equations, and no equality of localization universes is used. -/
theorem exists_mixedAffineSections_pullback_unit_normalization
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (g : T ⟶ S) :
    let F : ModuleCat.{u} Γ(S, ⊤) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
      tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
    let K : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
    let R := ModuleCat.restrictScalars.{u} g.appTop.hom
    let d : F ⋙ H ⟶ F ⋙ K ⋙ J ⋙ R :=
      Functor.whiskerRight (Functor.whiskerLeft F
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit) H
    ∀ [F.Additive] [H.Additive] [J.Additive] [K.Additive]
      (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ)
      (_hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat P),
    let C := (F.mapHomologicalComplex (.up ℤ)).obj P
    let Q : DerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) := DerivedCategory.Q.obj C
    let Y := ((F ⋙ K ⋙ J).mapHomologicalComplex (.up ℤ)).obj P
    ∃ b : (schemeDerivedGlobalSections T).obj ((derivedPullback g).obj Q) ≅
        DerivedCategory.Q.obj Y,
      mixedSectionsComplexUnit S C ≫
        (schemeDerivedGlobalSections S).map ((schemeHomPullbackAdjunction g).unit.app Q) ≫
          (mixedGlobalSectionsDirectImageIso g).hom.app ((derivedPullback g).obj Q) ≫
            (schemeGlobalScalarRestriction g).map b.hom =
      DerivedCategory.Q.map ((d.mapHomologicalComplex (.up ℤ)).app P) ≫
        R.mapDerivedCategoryFactors.inv.app Y := by
  classical
  intro F H J K R d hF hH hJ hK P hP C Q Y
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  let q := HomotopyCategory.quotient A (.up ℤ)
  let ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      K.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u, w})) g
  have hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso A (.up ℤ)) :=
    (Classical.choose (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w}))) g
  have : (tilde.functor Γ(S, ⊤)).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have hC : CochainComplex.IsKFlatTensor (R := S.sheaf) C := by
    change CochainComplex.IsKFlatTensor (R := S.sheaf)
      (((Scheme.Modules.restrictFunctor S.toSpecΓ).mapHomologicalComplex (.up ℤ)).obj
        (((tilde.functor Γ(S, ⊤)).mapHomologicalComplex (.up ℤ)).obj P))
    apply isKFlat_restrict S.toSpecΓ
    apply isKFlat_tilde Γ(S, ⊤) P
    intro N hN
    have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)).mp
        ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).mpr hN)).2
  have := hε
  have : IsIso (ε.app (q.obj C)) := mixedPullbackCounit_isIso g C ε hC
  let e : (derivedPullback g).obj Q ≅
      DerivedCategory.Q.obj ((K.mapHomologicalComplex (.up ℤ)).obj C) :=
    (derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso A).app C).symm ≪≫
      asIso (ε.app (q.obj C)) ≪≫
      DerivedCategory.Qh.mapIso ((K.mapHomotopyCategoryFactors (.up ℤ)).app C) ≪≫
      (DerivedCategory.quotientCompQhIso B).app _
  let TY := tilde.functor Γ(S, ⊤)
  let TX := tilde.functor Γ(T, ⊤)
  have : TX.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let RY := Scheme.Modules.restrictFunctor S.toSpecΓ
  let RX := Scheme.Modules.restrictFunctor T.toSpecΓ
  let kg := Spec.map g.appTop
  let aS := (Scheme.Modules.nonempty_tensorPullbackAdjunction S.toSpecΓ).some.leftAdjointUniq
    (Scheme.Modules.restrictAdjunction S.toSpecΓ)
  let aT := (Scheme.Modules.nonempty_tensorPullbackAdjunction T.toSpecΓ).some.leftAdjointUniq
    (Scheme.Modules.restrictAdjunction T.toSpecΓ)
  let square : RY ⋙ K ≅ Scheme.Modules.tensorPullback kg ⋙ RX :=
    Functor.isoWhiskerRight aS.symm K ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp g S.toSpecΓ).some.symm ≪≫
      eqToIso (congrArg Scheme.Modules.tensorPullback (Scheme.toSpecΓ_naturality g)) ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp T.toSpecΓ kg).some ≪≫
      Functor.isoWhiskerLeft _ aT
  let θ := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso g.appTop)
  let E := ModuleCat.extendScalars g.appTop.hom
  have : E.Additive := (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).left_adjoint_additive
  let FT := TX ⋙ RX
  have : RX.Additive := by
    change (Scheme.Modules.restrictFunctor T.toSpecΓ).Additive
    infer_instance
  have : FT.Additive := inferInstance
  let comparison : F ⋙ K ≅ E ⋙ FT :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft TY square ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight θ RX ≪≫
      Functor.associator _ _ _
  let δ : (K.mapHomologicalComplex (.up ℤ)).obj C ≅
      (FT.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj P) :=
    (NatIso.mapHomologicalComplex comparison (.up ℤ)).app P
  have : IsIso (mixedSectionsComplexUnit T
      ((FT.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj P))) :=
    mixedAffineChart_sectionsComplexUnit_isIso T _
  have : IsIso (mixedSectionsComplexUnit T ((K.mapHomologicalComplex (.up ℤ)).obj C)) :=
    mixedSectionsComplexUnit_isIso_of_iso T δ
  let sT : DerivedCategory.Q.obj Y ⟶
      (schemeDerivedGlobalSections T).obj
        (DerivedCategory.Q.obj ((K.mapHomologicalComplex (.up ℤ)).obj C)) :=
    mixedSectionsComplexUnit T ((K.mapHomologicalComplex (.up ℤ)).obj C)
  have : IsIso sT := by dsimp only [sT]; infer_instance
  let b : (schemeDerivedGlobalSections T).obj ((derivedPullback g).obj Q) ≅
      DerivedCategory.Q.obj Y :=
    (schemeDerivedGlobalSections T).mapIso e ≪≫ (asIso sT).symm
  refine ⟨b, ?_⟩
  have hu := Classical.choose_spec (exists_schemeDerivedAdjunction.{u, w} g
    (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) g)
    ε hε) (q.obj C) _ (𝟙 _)
  have h := mixedPullback_sections_counit_unit g C ε hu
  change mixedSectionsComplexUnit S C ≫
      (schemeDerivedGlobalSections S).map ((schemeHomPullbackAdjunction g).unit.app Q) ≫
      (mixedGlobalSectionsDirectImageIso g).hom.app ((derivedPullback g).obj Q) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeDerivedGlobalSections T).map e.hom) =
    DerivedCategory.Q.map ((d.mapHomologicalComplex (.up ℤ)).app P) ≫
      R.mapDerivedCategoryFactors.inv.app Y ≫
      (schemeGlobalScalarRestriction g).map sT at h
  have h' := cancel_right_iso _ _ _ ((schemeGlobalScalarRestriction g).map sT) h
  dsimp only [b, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv,
    Category.assoc] using h'

end AlgebraicGeometry
