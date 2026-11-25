/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # Scalar-extension unit on affine models

Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: new-affine-extension-model-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- K-flat extension models respect the extension adjunction unit.
Source: Stacks Project, perfect.tex, Tags 08DW(2) and 0AA7.
(blueprint: new-affine-extension-model-unit).
Proof: The ordinary tilde unit identifies X with M, so X is K-flat. Affine
acyclicity makes its sections comparison invertible, including for unbounded
complexes. Let s be the inverse of that comparison. The standard left-derived
extension is left adjoint to exact restriction. Identify the fixed extension
adjunction with this standard adjunction by the unit-compatible uniqueness
isomorphism. Its K-flat counit at X is invertible. Composing the extension
of s, the uniqueness isomorphism, and this counit gives a. The formula for
the derived adjunction unit, followed by the exact restriction comparison,
gives the displayed identity. Naturality of the unit moves s to the left.
All assertions also hold for the zero ring and the zero complex. -/
theorem exists_affineExtension_model_unit
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    [(@id (ModuleCat.{u} R ⥤
      SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)).Additive]
    [(ModuleCat.extendScalars.{u, u, u} (affineBaseRingMap g)).Additive]
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat M) :
    let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} R ⥤
        SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
    let K := T.obj M
    let X := ((affineGlobalSections (𝟙 (Spec R))).mapHomologicalComplex (.up ℤ)).obj K
    let Z := (affineDerivedGlobalSections (𝟙 (Spec R))).obj (DerivedCategory.Q.obj K)
    let E := ModuleCat.extendScalars.{u, u, u} (affineBaseRingMap g)
    let U := ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
    ∃ (s : Z ≅ DerivedCategory.Q.obj X)
      (a : (affineDerivedExtension g).obj Z ≅
        DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj X)),
      s.inv =
        (DerivedCategory.quotientCompQhIso _).inv.app X ≫
          (affineGlobalSections (𝟙 (Spec R))).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
          (affineGlobalSections (𝟙 (Spec R))).rightDerivedFunctor.map
            ((DerivedCategory.quotientCompQhIso _).hom.app K) ≫
          (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
            (DerivedCategory.Q.obj K) ∧
      (affineDerivedExtensionAdjunction g).unit.app Z ≫ U.mapDerivedCategory.map a.hom =
        s.hom ≫ DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj (affineBaseRingMap g)).mapHomologicalComplex
            (.up ℤ)).unit.app X) ≫
          U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
  dsimp only
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} R ⥤
      SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
      (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let K := T.obj M
  let S := affineGlobalSections (𝟙 (Spec R))
  let X := (S.mapHomologicalComplex (.up ℤ)).obj K
  let Z := (affineDerivedGlobalSections (𝟙 (Spec R))).obj (DerivedCategory.Q.obj K)
  let ρ := affineBaseRingMap g
  let E := ModuleCat.extendScalars.{u, u, u} ρ
  let U := ModuleCat.restrictScalars.{u} ρ
  let eX : M ≅ X := HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ tilde.isoTop (M.X i)) (by
      intro i j hij
      exact ((tilde.toTildeΓNatIso (R := R)).hom.naturality (M.d i j)).symm)
  have hX : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat X :=
    ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat.prop_iff_of_iso eX).mp hM
  have hS : IsIso (S.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) := by
    exact affineTildeDerivedSectionsUnit_isIso R
      ((HomotopyCategory.quotient _ (.up ℤ)).obj M)
  let s : Z ≅ DerivedCategory.Q.obj X :=
    ((DerivedCategory.quotientCompQhIso _).app X).symm ≪≫
      asIso (S.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≪≫
      S.rightDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso _).app K) ≪≫
      (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).app (DerivedCategory.Q.obj K) |>.symm
  have : (ModuleCat.extendScalars.{u, u, u} ρ).PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ α hα
    let N := (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).obj (𝟙_ _)
    have h := (CochainComplex.mixedTensor_kFlat_quasiIso ρ).1 N P Q α hα hP hQ
    let e := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor ρ).flip (𝟙_ (ModuleCat.{u} B))
    have h' : QuasiIso
        ((((ModuleCat.mixedTensor ρ).obj (𝟙_ (ModuleCat.{u} B))).mapHomologicalComplex
          (.up ℤ)).map α) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (e.app P) (e.app Q) (e.hom.naturality α).symm)).1 h
    let e₀ : (ModuleCat.mixedTensor ρ).obj (𝟙_ (ModuleCat.{u} B)) ≅
        ModuleCat.extendScalars.{u, u, u} ρ :=
      Functor.isoWhiskerLeft (ModuleCat.extendScalars ρ)
        (leftUnitorNatIso (ModuleCat.{u} B)) ≪≫ Functor.rightUnitor _
    let e₁ := NatIso.mapHomologicalComplex e₀ (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e₁.app P) (e₁.app Q) (e₁.hom.naturality α).symm)).1 h'
  let adj := ModuleCat.extendRestrictScalarsAdj ρ
  let b : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e := (affineDerivedExtensionAdjunction g).leftAdjointUniq b
  have : IsIso (E.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) :=
    E.isIso_leftDerivedFunctorCounit_app_of_kFlat X hX
  let q₀ := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app X
  let q₁ := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).app
    ((E.mapHomologicalComplex (.up ℤ)).obj X)
  let q₂ := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app
    ((U.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj X))
  let ε := E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  let d : E.leftDerivedFunctor.obj (DerivedCategory.Q.obj X) ≅
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj X) :=
    E.leftDerivedFunctor.mapIso q₀.symm ≪≫ asIso ε ≪≫ q₁
  let a := (affineDerivedExtension g).mapIso s ≪≫ e.app (DerivedCategory.Q.obj X) ≪≫ d
  have hfac := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))
    E.leftDerivedFunctorCounit U.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  have ht : b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) := by
    simp only [b, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc]
    erw [← U.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    erw [← Category.assoc, hfac]
    have hβ := NatTrans.congr_app
      U.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((E.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X))
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hβ
    rw [Category.assoc]
    erw [reassoc_of% hβ]
    simp only [Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hu := U.mapDerivedCategoryFactorsh_hom_app
    ((E.mapHomologicalComplex (.up ℤ)).obj X)
  have hquot : DerivedCategory.Qh.map
      ((U.mapHomotopyCategoryFactors (.up ℤ)).inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj X)) = 𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Qh.map_id _
  rw [hquot] at hu
  erw [Category.comp_id] at hu
  have hu' : U.mapDerivedCategory.map q₁.hom ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj X) =
      U.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
    have h := congrArg (fun z ↦ z ≫ q₂.hom) hu
    change U.mapDerivedCategoryFactorsh.hom.app
      ((E.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom =
      (U.mapDerivedCategory.map q₁.hom ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj X) ≫
          q₂.inv) ≫ q₂.hom at h
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    exact h.symm
  have hstd : b.unit.app (DerivedCategory.Q.obj X) ≫ U.mapDerivedCategory.map d.hom =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
    apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app
      ((E.mapHomologicalComplex (.up ℤ)).obj X))).mp
    apply (cancel_epi q₀.hom).mp
    have hn := b.unit.naturality q₀.hom
    change q₀.hom ≫ b.unit.app (DerivedCategory.Q.obj X) =
      b.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) at hn
    have hq := DerivedCategory.quotientCompQhIso_hom_naturality
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app X)
    have hd : E.leftDerivedFunctor.map q₀.hom ≫ d.hom = ε ≫ q₁.hom := by
      change (E.leftDerivedFunctor.mapIso q₀).hom ≫
        ((E.leftDerivedFunctor.mapIso q₀).inv ≫ ε ≫ q₁.hom) = _
      exact Iso.hom_inv_id_assoc _ _
    have hdnat : q₀.hom ≫ b.unit.app (DerivedCategory.Q.obj X) ≫
        U.mapDerivedCategory.map d.hom =
      b.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map ε ≫ U.mapDerivedCategory.map q₁.hom := by
      calc
        _ = b.unit.app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
          U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) ≫
            U.mapDerivedCategory.map d.hom := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ z ≫ U.mapDerivedCategory.map d.hom) hn
        _ = _ := by
          rw [← U.mapDerivedCategory.map_comp, hd, Functor.map_comp]
    calc
      _ = b.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
          U.mapDerivedCategory.map ε ≫ U.mapDerivedCategory.map q₁.hom ≫
            U.mapDerivedCategoryFactors.hom.app
              ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
          U.mapDerivedCategoryFactors.hom.app
            ((E.mapHomologicalComplex (.up ℤ)).obj X)) hdnat
      _ = b.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
          U.mapDerivedCategory.map ε ≫
          U.mapDerivedCategoryFactorsh.hom.app
            ((E.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
        exact congrArg (fun z ↦ b.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
          U.mapDerivedCategory.map ε ≫ z) hu'
      _ = DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ q₂.hom) ht
      _ = q₀.hom ≫ DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) := by
        erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
        exact hq
      _ = _ := by
        simp only [Category.assoc, Iso.inv_hom_id_app]
        erw [Category.comp_id]
  refine ⟨s, a, rfl, ?_⟩
  change (affineDerivedExtensionAdjunction g).unit.app Z ≫
    U.mapDerivedCategory.map
      ((affineDerivedExtension g).map s.hom ≫ e.hom.app (DerivedCategory.Q.obj X) ≫
        d.hom) = _
  have hn := (affineDerivedExtensionAdjunction g).unit.naturality s.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have he := (affineDerivedExtensionAdjunction g).unit_leftAdjointUniq_hom_app b
    (DerivedCategory.Q.obj X)
  calc
    _ = ((affineDerivedExtensionAdjunction g).unit.app Z ≫
        U.mapDerivedCategory.map ((affineDerivedExtension g).map s.hom)) ≫
      U.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj X)) ≫
        U.mapDerivedCategory.map d.hom := by
      rw [Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
    _ = s.hom ≫ (affineDerivedExtensionAdjunction g).unit.app (DerivedCategory.Q.obj X) ≫
        U.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj X)) ≫
          U.mapDerivedCategory.map d.hom := by
      rw [← hn]
      simp only [Category.assoc]
    _ = s.hom ≫ b.unit.app (DerivedCategory.Q.obj X) ≫ U.mapDerivedCategory.map d.hom :=
      by simpa only [Category.assoc] using
        congrArg (fun z ↦ s.hom ≫ z ≫ U.mapDerivedCategory.map d.hom) he
    _ = _ := congrArg (fun z ↦ s.hom ≫ z) hstd

end AlgebraicGeometry
