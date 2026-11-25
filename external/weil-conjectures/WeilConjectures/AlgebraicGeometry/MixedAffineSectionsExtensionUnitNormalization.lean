/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsComplexUnit
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # The source affine model and its extension unit normalization
Source: Stacks Project, Tags 06Z0, 08DW(2) and 0AA7.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def normalizationChartSectionsIso (Y : Scheme.{u}) [IsAffine Y] :
    SheafOfModules.evaluation.{u} Y.ringCatSheaf (Opposite.op ⊤) ≅
      SheafOfModules.pushforward Y.isoSpec.hom.toRingCatSheafHom ⋙
        moduleSpecΓFunctor (R := Γ(Y, ⊤)) := by
  refine NatIso.ofComponents (fun N ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext x
    change (Y.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom r)) •
      (show Γ(N, ⊤) from x) = (show Γ(Y, ⊤) from r) • (show Γ(N, ⊤) from x)
    congr 1
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso Γ(Y, ⊤)).inv_hom_id_apply r
  · intro N N' f
    ext x
    rfl

private noncomputable def normalizationChartModuleIso (Y : Scheme.{u}) [IsAffine Y] :
    𝟭 (ModuleCat.{u} Γ(Y, ⊤)) ≅
      (tilde.functor Γ(Y, ⊤) ⋙ restrictFunctor Y.toSpecΓ) ⋙
        RingedSpace.globalSectionsFunctor Y.toRingedSpace := by
  let F := pushforward Y.isoSpec.hom
  let G := pushforward Y.isoSpec.inv
  let e : Y.Modules ≌ (Spec Γ(Y, ⊤)).Modules :=
    CategoryTheory.Equivalence.mk F G
      (pushforwardComp Y.isoSpec.hom Y.isoSpec.inv ≪≫
        pushforwardCongr Y.isoSpec.hom_inv_id ≪≫ pushforwardId Y).symm
      (pushforwardComp Y.isoSpec.inv Y.isoSpec.hom ≪≫
        pushforwardCongr Y.isoSpec.inv_hom_id ≪≫ pushforwardId (Spec Γ(Y, ⊤)))
  have : (pushforward Y.toSpecΓ).IsEquivalence := e.isEquivalence_functor
  let L := restrictFunctor Y.toSpecΓ
  let H := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let S := moduleSpecΓFunctor (R := Γ(Y, ⊤))
  let j : L ⋙ H ≅ S :=
    Functor.isoWhiskerLeft L (normalizationChartSectionsIso Y) ≪≫
      (Functor.associator L (pushforward Y.toSpecΓ) S).symm ≪≫
      Functor.isoWhiskerRight (asIso (restrictAdjunction Y.toSpecΓ).unit).symm S ≪≫
      Functor.leftUnitor S
  exact tilde.toTildeΓNatIso ≪≫ Functor.isoWhiskerLeft (tilde.functor Γ(Y, ⊤)) j.symm ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- The extension counit computes the affine chart source, and intertwines Hom transposes.
Source: Stacks Project, Tags 06Z0, 08DW(2), 0AA7.
(blueprint: lem-sc-mixed-affine-extension-unit-normalization).

Proof: The ordinary affine tilde unit identifies H(F(P)) with P termwise, so this
complex is K-flat. Its left-derived extension counit is therefore invertible.
Identify the fixed mixedGlobalExtension adjunction with the derived extension
adjunction by left-adjoint uniqueness, preserving its unit. The source comparison a
is the inverse of extension applied to mixedSectionsComplexUnit, followed by this
counit. The affine sections comparison is invertible by the affine chart sections
unit theorem. Apply derivedη_fac_app to extension/restriction, inserting the exact
restriction comparison and quotient-to-homotopy factors. This proves the formula for
the unit. Postcompose with an arbitrary complex map f and use naturality of the
exact restriction comparison to obtain the displayed equality. It is uniform in Z
and f and uses no pullback, Leray comparison, or ordinary comparison c. Zero rings,
zero complexes and zero morphisms satisfy the same unit and naturality equations. -/
theorem exists_mixedAffineSections_extension_unit_normalization
    {S T : Scheme.{u}} [IsAffine S] (g : T ⟶ S) :
    let F : ModuleCat.{u} Γ(S, ⊤) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
      tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let E := ModuleCat.extendScalars.{u, u, u} g.appTop.hom
    let R := ModuleCat.restrictScalars.{u} g.appTop.hom
    ∀ [F.Additive] [H.Additive] [E.Additive]
      (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ)
      (_hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat P),
    let C := (F.mapHomologicalComplex (.up ℤ)).obj P
    let X := ((F ⋙ H).mapHomologicalComplex (.up ℤ)).obj P
    ∃ a : (mixedGlobalExtension g).obj
        ((schemeDerivedGlobalSections S).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj (((F ⋙ H ⋙ E).mapHomologicalComplex (.up ℤ)).obj P),
    ∀ (Z : CochainComplex (ModuleCat.{u} Γ(T, ⊤)) ℤ)
      (f : ((E.mapHomologicalComplex (.up ℤ)).obj X) ⟶ Z),
      mixedSectionsComplexUnit S C ≫
          (mixedGlobalExtensionAdjunction g).homEquiv _ _
            (a.hom ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).mapHomologicalComplex
            (.up ℤ)).unit.app X ≫
              (R.mapHomologicalComplex (.up ℤ)).map f) ≫
          R.mapDerivedCategoryFactors.inv.app Z := by
  classical
  dsimp only
  intro instF instH instE P hP
  let F := tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
  let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
  let E := ModuleCat.extendScalars.{u, u, u} g.appTop.hom
  let R := ModuleCat.restrictScalars.{u} g.appTop.hom
  let lAdj : mixedGlobalExtension g ⊣ R.mapDerivedCategory :=
    mixedGlobalExtensionAdjunction g
  let C := (F.mapHomologicalComplex (.up ℤ)).obj P
  let X : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ :=
    ((F ⋙ H).mapHomologicalComplex (.up ℤ)).obj P
  let Y : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)) :=
    (schemeDerivedGlobalSections S).obj (DerivedCategory.Q.obj C)
  let eX : P ≅ X :=
    ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P).symm ≪≫
      (NatIso.mapHomologicalComplex
        (Scheme.Modules.normalizationChartModuleIso S) (.up ℤ)).app P
  have hX : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat X :=
    ((HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat.prop_iff_of_iso
      eX).mp hP
  have : IsIso (mixedSectionsComplexUnit S C) :=
    mixedAffineChart_sectionsComplexUnit_isIso S P
  let s : Y ≅ DerivedCategory.Q.obj X := (asIso (mixedSectionsComplexUnit S C)).symm
  have : (ModuleCat.extendScalars.{u, u, u} g.appTop.hom).PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ α hα
    let U₀ := CategoryTheory.MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} Γ(T, ⊤))
    let N := (HomologicalComplex.single (ModuleCat.{u} Γ(T, ⊤)) (.up ℤ) 0).obj U₀
    have h := (CochainComplex.mixedTensor_kFlat_quasiIso g.appTop.hom).1 N P Q α hα hP hQ
    let e := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor g.appTop.hom).flip U₀
    have h' : QuasiIso
        ((((ModuleCat.mixedTensor g.appTop.hom).obj
          U₀).mapHomologicalComplex
          (.up ℤ)).map α) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (e.app P) (e.app Q) (e.hom.naturality α).symm)).1 h
    let e₀ : (ModuleCat.mixedTensor g.appTop.hom).obj U₀ ≅
        ModuleCat.extendScalars.{u, u, u} g.appTop.hom :=
      Functor.isoWhiskerLeft (ModuleCat.extendScalars g.appTop.hom)
        (CategoryTheory.MonoidalCategory.leftUnitorNatIso (ModuleCat.{u} Γ(T, ⊤))) ≪≫
          Functor.rightUnitor _
    let e₁ := NatIso.mapHomologicalComplex e₀ (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e₁.app P) (e₁.app Q) (e₁.hom.naturality α).symm)).1 h'
  let adj := ModuleCat.extendRestrictScalarsAdj g.appTop.hom
  let t := DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
    R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X)
  let k := (lAdj.homEquiv (DerivedCategory.Q.obj X)
    (DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj X))).symm t
  have : IsIso k :=
    Adjunction.isIso_cochainTranspose_of_kFlat E R adj lAdj X hX
  let a := (mixedGlobalExtension g).mapIso s ≪≫ asIso k
  have ha : lAdj.unit.app Y ≫ R.mapDerivedCategory.map a.hom = s.hom ≫ t := by
    change lAdj.homEquiv _ _
      ((mixedGlobalExtension g).map s.hom ≫ (lAdj.homEquiv _ _).symm t) = _
    rw [lAdj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  refine ⟨a, ?_⟩
  intro Z f
  change s.inv ≫ lAdj.homEquiv _ _ (a.hom ≫ DerivedCategory.Q.map f) = _
  rw [lAdj.homEquiv_unit]
  change s.inv ≫ lAdj.unit.app Y ≫
    R.mapDerivedCategory.map (a.hom ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app X ≫
        (R.mapHomologicalComplex (.up ℤ)).map f) ≫ R.mapDerivedCategoryFactors.inv.app Z
  rw [Functor.map_comp]
  erw [reassoc_of% ha]
  simp only [Iso.inv_hom_id_assoc]
  dsimp only [t]
  rw [Category.assoc]
  erw [← R.mapDerivedCategoryFactors.inv.naturality]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

end AlgebraicGeometry
