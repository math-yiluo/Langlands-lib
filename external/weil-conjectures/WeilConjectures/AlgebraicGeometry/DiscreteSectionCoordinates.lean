/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Coordinates for one discrete coefficient section

Source: Stacks, Tags 03CY and 00YV; the monoidal constant-sheaf comparison and
weakly-etale localization in the scalar-entry step of local matrix descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- The constant scalar at the profinite point, followed by the constant-sheaf adjunction.
This is an explicit section; it uses neither a local lift nor an existence theorem.
Source: the constant-sheaf adjunction, Stacks Tag 00YV
(auxiliary; not a blueprint node). -/
def discretePointScalarSection (A : Type u) [CommRing A] (c : ULift.{u + 1} A) :
    𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ discreteObj A :=
  Functor.LaxMonoidal.ε (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      (AddCommGrpCat.ofHom ((zmultiplesHom _
        ((toSheafify (coherentTopology Profinite.{u})
          ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
            (op (Profinite.of PUnit.{u + 1})) c)).comp AddEquiv.ulift.toAddMonoidHom)) ≫
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app (discreteObj A)

private abbrev forgetCRAb : CommRingCat.{u + 1} ⥤ Ab.{u + 1} :=
  forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}

private instance schemeAbSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) Ab.{u + 1} := inferInstance

private instance schemeRingSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} := inferInstance

private instance pointAbSheafify :
    HasWeakSheafify (coherentTopology Profinite.{u}) Ab.{u + 1} := inferInstance

private instance pointRingSheafify :
    HasWeakSheafify (coherentTopology Profinite.{u}) CommRingCat.{u + 1} := inferInstance

private instance smallRingSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1} := inferInstance

private instance pointPreserves :
    (coherentTopology Profinite.{u}).PreservesSheafification forgetCRAb.{u} :=
  GrothendieckTopology.instPreservesSheafification _ _

private instance schemePreserves (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification forgetCRAb.{u} :=
  GrothendieckTopology.instPreservesSheafification _ _

private theorem forgetConstant_unit {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{u + 1}]
    [HasWeakSheafify J Ab.{u + 1}] [J.HasSheafCompose forgetCRAb.{u}]
    [J.PreservesSheafification forgetCRAb.{u}]
    (A : Type u) [CommRing A] (T : Cᵒᵖ) (c : ULift.{u + 1} A) :
    ((constantCommuteCompose J forgetCRAb).hom.app
        (CommRingCat.of (ULift.{u + 1} A))).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app T c) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app T c := by
  let B := CommRingCat.of (ULift.{u + 1} A)
  let e := (constantCommuteCompose J forgetCRAb).app B
  have hf : toSheafify J ((Functor.const Cᵒᵖ).obj (forgetCRAb.obj B)) ≫ e.inv.hom =
      Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj B)) forgetCRAb := by
    change _ ≫ (sheafifyMap J (Functor.constComp Cᵒᵖ B forgetCRAb).inv ≫
      (sheafifyComposeIso J forgetCRAb _).hom) = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
      sheafComposeIso_hom_fac]
    ext V a
    rfl
  have hp := ConcreteCategory.congr_hom (congr_app hf T) c
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app T) e.inv_hom_id)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (forgetCRAb.obj B))).app T c)
  change e.inv.hom.app T
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (forgetCRAb.obj B))).app T c) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app T c at hp
  change e.hom.hom.app T (e.inv.hom.app T _) = _ at hi
  exact (congrArg (e.hom.hom.app T) hp).symm.trans hi

private def coefficientAbIso (A : Type u) [CommRing A] (X : Scheme.{u}) :
    (sheafCompose (Scheme.ProEt.topology X) forgetCRAb).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} A))) ≅ condensedRingObj (discreteObj A) X :=
  (constantCommuteCompose (Scheme.ProEt.topology X) forgetCRAb).app _ ≪≫
    (constantSchemeIso X).app _ ≪≫ (upperStarFromPoint X).mapIso
      ((constantCommuteCompose (coherentTopology Profinite.{u}) forgetCRAb).app _).symm

private def unitSectionEquiv {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {T : C} (hT : IsTerminal T) (F : Sheaf J Ab.{u + 1}) :
    (𝟙_ (Sheaf J Ab.{u + 1}) ⟶ F) ≃ F.obj.obj (op T) :=
  (Iso.homCongr (Functor.Monoidal.εIso (constantSheaf J Ab.{u + 1}))
    (Iso.refl F)).trans
      (((constantSheafAdj J Ab.{u + 1} hT).homEquiv _ _).trans
        (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom _).symm))

private def zHom (M : Ab.{u + 1}) (a : M) : 𝟙_ Ab.{u + 1} ⟶ M :=
  AddCommGrpCat.ofHom ((zmultiplesHom _ a).comp AddEquiv.ulift.toAddMonoidHom)

private theorem unitSectionEquiv_symm {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {T : C} (hT : IsTerminal T) (F : Sheaf J Ab.{u + 1}) (a : F.obj.obj (op T)) :
    (unitSectionEquiv J hT F).symm a =
      Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) ≫
        (constantSheaf J Ab.{u + 1}).map (zHom _ a) ≫
          (constantSheafAdj J Ab.{u + 1} hT).counit.app F := by
  change Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) ≫
    ((constantSheafAdj J Ab.{u + 1} hT).homEquiv _ _).symm (zHom _ a) = _
  rw [Adjunction.homEquiv_counit]
  rfl

private theorem unitSectionEquiv_symm_naturality
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {T : C} (hT : IsTerminal T) {F G : Sheaf J Ab.{u + 1}}
    (f : F ⟶ G) (a : F.obj.obj (op T)) :
    (unitSectionEquiv J hT F).symm a ≫ f =
      (unitSectionEquiv J hT G).symm (f.hom.app (op T) a) := by
  have hz : zHom _ a ≫ f.hom.app (op T) = zHom _ (f.hom.app (op T) a) := by
    ext n
    simp [zHom]
  rw [unitSectionEquiv_symm, unitSectionEquiv_symm]
  calc
    _ = Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) ≫
        (constantSheaf J Ab.{u + 1}).map (zHom _ a) ≫
          (constantSheaf J Ab.{u + 1}).map (f.hom.app (op T)) ≫
            (constantSheafAdj J Ab.{u + 1} hT).counit.app G := by
      simp only [Category.assoc]
      rw [← (constantSheafAdj J Ab.{u + 1} hT).counit_naturality]
      rfl
    _ = Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) ≫
        (constantSheaf J Ab.{u + 1}).map (zHom _ a ≫ f.hom.app (op T)) ≫
          (constantSheafAdj J Ab.{u + 1} hT).counit.app G := by
      rw [(constantSheaf J Ab.{u + 1}).map_comp]
      simp only [Category.assoc]
    _ = _ := by rw [hz]

private theorem unitSectionEquiv_constant
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {T : C} (hT : IsTerminal T) (M : Ab.{u + 1}) (a : M) :
    (unitSectionEquiv J hT ((constantSheaf J Ab.{u + 1}).obj M)).symm
        ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) a) =
      Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) ≫
        (constantSheaf J Ab.{u + 1}).map (zHom _ a) := by
  have hunit : (constantSheafAdj J Ab.{u + 1} hT).unit.app M =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) := by
    simp [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj]
  have hz : zHom (((constantSheaf J Ab.{u + 1}).obj M).obj.obj (op T))
      ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) a) =
      zHom M a ≫ (constantSheafAdj J Ab.{u + 1} hT).unit.app M := by
    ext n
    simp [zHom, hunit]
    rfl
  rw [unitSectionEquiv_symm, hz, (constantSheaf J Ab.{u + 1}).map_comp]
  simp only [Category.assoc]
  rw [(constantSheafAdj J Ab.{u + 1} hT).left_triangle_components, Category.comp_id]

private instance overMapContinuous {Y : Scheme.{u}} (U : Y.ProEt) :
    (MorphismProperty.Over.map ⊤ U.prop).IsContinuous
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology Y) :=
  Scheme.ProEt.isContinuous_overMap U.prop

private instance overMapCocontinuous {Y : Scheme.{u}} (U : Y.ProEt) :
    (MorphismProperty.Over.map ⊤ U.prop).IsCocontinuous
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology Y) :=
  Scheme.ProEt.isCocontinuous_overMap U.prop

private def ringIsoEquiv {R S : CommRingCat.{u + 1}} (e : R ≅ S) : R ≃ S where
  toFun := e.hom
  invFun := e.inv
  left_inv a := ConcreteCategory.congr_hom e.hom_inv_id a
  right_inv a := ConcreteCategory.congr_hom e.inv_hom_id a

private def localConstantIso (A : Type u) [CommRing A] {Y : Scheme.{u}} (U : Y.ProEt) :
    (constantSheaf (Scheme.ProEt.topology U.left) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A)) ≅
    ((MorphismProperty.Over.map ⊤ U.prop).sheafPushforwardContinuous
      CommRingCat.{u + 1} (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology Y)).obj
      ((constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} A))) :=
  ((MorphismProperty.Over.map ⊤ U.prop).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u + 1} (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology Y)).app
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))

private def localObjectIso {Y : Scheme.{u}} (U : Y.ProEt) :
    (MorphismProperty.Over.map ⊤ U.prop).obj (Scheme.ProEt.mk (𝟙 U.left)) ≅ U :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change U.hom = 𝟙 U.left ≫ U.hom
    exact (Category.id_comp _).symm)

private instance smallDownCocontinuous (Y : Scheme.{u}) :
    (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} Y ⥤ Y.ProEt).IsCocontinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y) (Scheme.ProEt.topology Y) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  have : e.inverse.IsCoverDense (Scheme.ProEt.topology Y) := inferInstance
  exact inferInstanceAs (e.inverse.IsCocontinuous
    (e.inverse.inducedTopology (Scheme.ProEt.topology Y)) (Scheme.ProEt.topology Y))

private def smallConstantIso (A : Type u) [CommRing A] (Y : Scheme.{u}) :
    (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
      CommRingCat.{u + 1}).obj (CommRingCat.of (ULift.{u + 1} A)) ≅
    ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} Y ⥤
      Y.ProEt).sheafPushforwardContinuous
      CommRingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} Y) (Scheme.ProEt.topology Y)).obj
      ((constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} A))) :=
  ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} Y ⥤
    Y.ProEt).pushforwardContinuousSheafificationCompatibility
     CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y) (Scheme.ProEt.topology Y)).app
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))

private def coordinateEquiv (A : Type u) [CommRing A] {Y : Scheme.{u}}
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) :
    ((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
      CommRingCat.{u + 1}).obj (CommRingCat.of (ULift.{u + 1} A))).obj.obj (op U) ≃
      (𝟙_ (Sheaf (Scheme.ProEt.topology (AsSmall.down.obj U).left) Ab.{u + 1}) ⟶
        condensedRingObj (discreteObj A) (AsSmall.down.obj U).left) :=
  let W := AsSmall.down.obj U
  let R := (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} A))
  (ringIsoEquiv
    ((sheafSections _ _).obj (op U) |>.mapIso (smallConstantIso A Y))).trans
    ((ringIsoEquiv (R.obj.mapIso (localObjectIso W).op)).trans
      ((ringIsoEquiv
        ((sheafSections _ _).obj (op (Scheme.ProEt.mk (𝟙 W.left))) |>.mapIso
          (localConstantIso A W).symm)).trans
        ((unitSectionEquiv (Scheme.ProEt.topology W.left)
          (MorphismProperty.Over.mkIdTerminal _ W.left) _).symm.trans
            (Iso.homCongr (Iso.refl _) (coefficientAbIso A W.left)))))

private def constantScalarSection (A : Type u) [CommRing A] (X : Scheme.{u})
    (c : ULift.{u + 1} A) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶
      condensedRingObj (discreteObj A) X :=
  (unitSectionEquiv (Scheme.ProEt.topology X)
    (MorphismProperty.Over.mkIdTerminal _ X) _).symm
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
          (op (Scheme.ProEt.mk (𝟙 X))) c) ≫ (coefficientAbIso A X).hom

private theorem constantScalarSection_formula (A : Type u) [CommRing A] (X : Scheme.{u})
    (c : ULift.{u + 1} A) :
    constantScalarSection A X c =
      Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
        (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
          (zHom (AddCommGrpCat.of (ULift.{u + 1} A)) c) ≫
        (constantSchemeIso X).hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫
        (upperStarFromPoint X).map
          ((constantCommuteCompose (coherentTopology Profinite.{u}) forgetCRAb).inv.app
            (CommRingCat.of (ULift.{u + 1} A))) := by
  dsimp only [constantScalarSection, coefficientAbIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, unitSectionEquiv_symm_naturality]
  erw [forgetConstant_unit (Scheme.ProEt.topology X) A _ c]
  erw [unitSectionEquiv_constant (Scheme.ProEt.topology X)
    (MorphismProperty.Over.mkIdTerminal _ X) (AddCommGrpCat.of (ULift.{u + 1} A)) c]
  rfl

private theorem pointScalarSection_formula (A : Type u) [CommRing A]
    (c : ULift.{u + 1} A) :
    discretePointScalarSection A c =
      Functor.LaxMonoidal.ε (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
        (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
          (zHom (AddCommGrpCat.of (ULift.{u + 1} A)) c) ≫
        ((constantCommuteCompose (coherentTopology Profinite.{u}) forgetCRAb).inv.app
          (CommRingCat.of (ULift.{u + 1} A))) := by
  let J := coherentTopology Profinite.{u}
  let e := (constantCommuteCompose J forgetCRAb).app
    (CommRingCat.of (ULift.{u + 1} A))
  have h := unitSectionEquiv_symm_naturality J Profinite.isTerminalPUnit e.hom
    ((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} A)))).app (op (Profinite.of PUnit.{u + 1})) c)
  change _ = (unitSectionEquiv J Profinite.isTerminalPUnit _).symm
    (e.hom.hom.app (op (Profinite.of PUnit.{u + 1})) _) at h
  erw [forgetConstant_unit J A _ c] at h
  erw [unitSectionEquiv_constant J Profinite.isTerminalPUnit
    (AddCommGrpCat.of (ULift.{u + 1} A)) c] at h
  have h' := congrArg (fun k ↦ k ≫ e.inv) h
  simp only [Category.assoc, e.hom_inv_id, Category.comp_id] at h'
  calc
    discretePointScalarSection A c =
        (unitSectionEquiv J Profinite.isTerminalPUnit (discreteObj A)).symm
          ((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} A)))).app (op (Profinite.of PUnit.{u + 1})) c) := by
      rw [unitSectionEquiv_symm]
      rfl
    _ = _ := h'

private theorem constantScalarSection_point (A : Type u) [CommRing A] (X : Scheme.{u})
    (c : ULift.{u + 1} A) :
    constantScalarSection A X c =
      Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (discretePointScalarSection A c) := by
  rw [constantScalarSection_formula, pointScalarSection_formula]
  have hn := (constantSchemeIso X).hom.naturality
    (zHom (AddCommGrpCat.of (ULift.{u + 1} A)) c)
  erw [reassoc_of% hn]
  rw [NatTrans.IsMonoidal.unit_assoc]
  simp only [Functor.LaxMonoidal.comp_ε, Functor.map_comp, Category.assoc]

private theorem coordinateEquiv_unit (A : Type u) [CommRing A] {Y : Scheme.{u}}
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (c : ULift.{u + 1} A) :
    coordinateEquiv A U
        ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
          ((Functor.const (Scheme.coefficientProEtaleSiteModel.{u, u} Y)ᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} A)))).app (op U) c) =
      constantScalarSection A (AsSmall.down.obj U).left c := by
  let W := AsSmall.down.obj U
  let B := CommRingCat.of (ULift.{u + 1} A)
  let R := (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj B
  let T := Scheme.ProEt.mk (𝟙 W.left)
  have hs := ConcreteCategory.congr_hom (congr_app
    ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} Y ⥤
      Y.ProEt).toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} Y) (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj B)) (op U)) c
  have ho := ConcreteCategory.congr_hom
    ((toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).naturality
      (localObjectIso W).op.hom) c
  have hl := ConcreteCategory.congr_hom (congr_app
    ((MorphismProperty.Over.map ⊤ W.prop).toSheafify_pullbackSheafificationCompatibility
      CommRingCat.{u + 1} (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj B)) (op T)) c
  have hli := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op T)) (localConstantIso A W).hom_inv_id)
      ((toSheafify (Scheme.ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj B)).app (op T) c)
  change (𝟙 _ ≫ (unitSectionEquiv (Scheme.ProEt.topology W.left)
    (MorphismProperty.Over.mkIdTerminal _ W.left)
      ((sheafCompose (Scheme.ProEt.topology W.left) forgetCRAb).obj
        ((constantSheaf (Scheme.ProEt.topology W.left) CommRingCat.{u + 1}).obj B))).symm
      ((localConstantIso A W).inv.hom.app (op T)
        (R.obj.map (localObjectIso W).op.hom
          ((smallConstantIso A Y).hom.hom.app (op U) _))) ≫
        (coefficientAbIso A W.left).hom) = _
  change (smallConstantIso A Y).hom.hom.app (op U)
    ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
      ((Functor.const (Scheme.coefficientProEtaleSiteModel.{u, u} Y)ᵒᵖ).obj B)).app
        (op U) c) =
      (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app
        (op W) c at hs
  erw [hs]
  change (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app
    (op ((MorphismProperty.Over.map ⊤ W.prop).obj T)) c =
      R.obj.map (localObjectIso W).op.hom
        ((toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app
          (op W) c) at ho
  erw [← ho]
  change (localConstantIso A W).hom.hom.app (op T)
    ((toSheafify (Scheme.ProEt.topology W.left)
      ((Functor.const W.left.ProEtᵒᵖ).obj B)).app (op T) c) =
      (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app
        (op ((MorphismProperty.Over.map ⊤ W.prop).obj T)) c at hl
  erw [← hl]
  change (localConstantIso A W).inv.hom.app (op T)
    ((localConstantIso A W).hom.hom.app (op T) _) = _ at hli
  erw [hli]
  rfl

private theorem unitSectionEquiv_symm_fac
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {T : C} (hT : IsTerminal T) (F : Sheaf J Ab.{u + 1}) (a : F.obj.obj (op T)) :
    Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
      ((unitSectionEquiv J hT F).symm a).hom =
        (Functor.const Cᵒᵖ).map (zHom _ a) ≫
          (constantPresheafAdj Ab.{u + 1} hT).counit.app F.obj := by
  have hε : Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
      (Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1})).hom =
        toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ Ab.{u + 1})) := by
    have hC : Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) =
        Functor.LaxMonoidal.ε (presheafToSheaf J Ab.{u + 1}) := by
      change _ ≫ (presheafToSheaf J Ab.{u + 1}).map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hC, ← (sheafificationAdjunction J Ab.{u + 1}).unit_app_unit_comp_map_η]
    change (_ ≫ (sheafToPresheaf J Ab.{u + 1}).map
      (Functor.OplaxMonoidal.η (presheafToSheaf J Ab.{u + 1}))) ≫
        (sheafToPresheaf J Ab.{u + 1}).map
          (Functor.LaxMonoidal.ε (presheafToSheaf J Ab.{u + 1})) = _
    rw [Category.assoc, ← Functor.map_comp, Functor.Monoidal.η_ε,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  change _ ≫ (Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) ≫
    ((constantSheafAdj J Ab.{u + 1} hT).homEquiv _ _).symm (zHom _ a)).hom = _
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, hε,
    constantSheafAdj, Adjunction.comp_homEquiv]
  change ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _)
    (((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).symm
      (((constantPresheafAdj Ab.{u + 1} hT).homEquiv _ _).symm (zHom _ a))) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_counit]
  rfl

private theorem unitSectionEquiv_restriction
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J Ab.{u + 1}] [HasWeakSheafify K Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    [G.IsContinuous J K] {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)
    (F : Sheaf K Ab.{u + 1}) (a : F.obj.obj (op S)) :
    Functor.LaxMonoidal.ε (G.sheafPushforwardContinuous Ab.{u + 1} J K) ≫
      (G.sheafPushforwardContinuous Ab.{u + 1} J K).map
        ((unitSectionEquiv K hS F).symm a) =
      (unitSectionEquiv J hT
        ((G.sheafPushforwardContinuous Ab.{u + 1} J K).obj F)).symm
          (F.obj.map (hS.from (G.obj T)).op a) := by
  apply Sheaf.hom_ext_of_ε_comp
  apply NatTrans.ext
  funext V
  change (Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1})).app V ≫
    (Functor.LaxMonoidal.ε (G.sheafPushforwardContinuous Ab.{u + 1} J K)).hom.app V ≫
      ((unitSectionEquiv K hS F).symm a).hom.app (G.op.obj V) = _
  rw [← Category.assoc,
    Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app]
  have hL := congr_app (unitSectionEquiv_symm_fac K hS F a) (G.op.obj V)
  have hR := congr_app (unitSectionEquiv_symm_fac J hT
    ((G.sheafPushforwardContinuous Ab.{u + 1} J K).obj F)
      (F.obj.map (hS.from (G.obj T)).op a)) V
  simp only [NatTrans.comp_app] at hL hR
  simp only [NatTrans.comp_app]
  erw [hL, hR]
  change zHom _ a ≫ F.obj.map (hS.from (G.obj V.unop)).op =
    zHom _ (F.obj.map (hS.from (G.obj T)).op a) ≫
      F.obj.map (G.map (hT.from V.unop)).op
  have hz : zHom _ (F.obj.map (hS.from (G.obj T)).op a) =
      zHom _ a ≫ F.obj.map (hS.from (G.obj T)).op := by
    ext n
    simp [zHom]
  rw [hz, Category.assoc, ← Functor.map_comp, ← op_comp]
  congr 2
  exact congrArg Quiver.Hom.op (hS.hom_ext _ _)

attribute [irreducible] unitSectionEquiv

private theorem constantNatTrans_ext {C D : Type*} [Category C] [Category D]
    {M : D} {P : Cᵒᵖ ⥤ D} {T : C} (hT : IsTerminal T)
    (a b : (Functor.const Cᵒᵖ).obj M ⟶ P) (h : a.app (op T) = b.app (op T)) :
    a = b := by
  ext X
  have ha := a.naturality (hT.from X.unop).op
  have hb := b.naturality (hT.from X.unop).op
  dsimp only [Functor.const_obj_map] at ha hb
  erw [Category.id_comp] at ha hb
  rw [h] at ha
  exact ha.trans hb.symm

private def constantCoefficientMap (M : Ab.{u + 1})
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (e : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj M ⟶ R)
    (X : Scheme.{u}) :
    (Functor.const X.ProEtᵒᵖ).obj M ⟶ (condensedRingObj R X).obj :=
  toSheafify (Scheme.ProEt.topology X) _ ≫
    ((constantSchemeIso X).hom.app M ≫ (upperStarFromPoint X).map e).hom

private theorem constantCoefficientMap_pushforward (M : Ab.{u + 1})
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (e : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj M ⟶ R)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantCoefficientMap M R e Y ≫ (condensedPushforwardHom R f).hom =
      Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
        (constantCoefficientMap M R e X) := by
  apply constantNatTrans_ext
    (proEtIsTerminal
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ Y)).obj
        (proEtTerminal specZ.{u})))
  exact CondensedRing.constantScheme_pushforward M R e Y X f

private def localizedCoefficientMap (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : WeaklyEtale f) :
    (localizationRestriction Ab.{u + 1} f hf).obj (condensedRingObj R Y) ⟶
      condensedRingObj R X :=
  (upperStarIsoLocalizationRestriction Ab.{u + 1} f hf).inv.app
      (condensedRingObj R Y) ≫ (upperStarFromPointComp f).hom.app R

private theorem leftAdjointUniq_inv_comp {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G)
    {a : C} {b : D} (t : F.obj a ⟶ b) :
    (adj₁.leftAdjointUniq adj₂).inv.app a ≫ t =
      F'.map (adj₁.unit.app a ≫ G.map t) ≫ adj₂.counit.app b := by
  rw [Adjunction.leftAdjointUniq_inv_app,
    ← Adjunction.leftAdjointUniq_hom_app_counit adj₂ adj₁ b,
    ← Category.assoc, (adj₂.leftAdjointUniq adj₁).hom.naturality, Category.assoc]
  congr 1
  have hn : F.map (G.map t) ≫ adj₁.counit.app b =
      adj₁.counit.app (F.obj a) ≫ t := adj₁.counit.naturality t
  have ht : F.map (adj₁.unit.app a) ≫ adj₁.counit.app (F.obj a) = 𝟙 (F.obj a) :=
    adj₁.left_triangle_components a
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn,
    ← Category.assoc, ht]
  exact (Category.id_comp t).symm

private theorem localizedCoefficientMap_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : WeaklyEtale f) :
    localizedCoefficientMap R f hf =
      (localizationRestriction Ab.{u + 1} f hf).map (condensedPushforwardHom R f) ≫
        (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f hf).counit.app _ := by
  exact leftAdjointUniq_inv_comp (upperStarLowerStarAdjunction Ab.{u + 1} f)
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f hf)
    (condensedPullbackHom R f)

private theorem pushforwardAdjunction_counit_app
    {C D B : Type*} [Category C] [Category D] [Category B]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [G.IsContinuous K J] (P : Sheaf J B) (V : Cᵒᵖ) :
    ((adj.sheafPushforwardContinuous J K).counit.app P).hom.app V =
      P.obj.map (adj.unit.app V.unop).op := by
  simp only [Functor.comp_obj, Functor.id_obj,
    Adjunction.sheafPushforwardContinuous_counit_app_hom_app, op_unop]

private theorem constantMap_localization
    {C D B : Type*} [Category C] [Category D] [Category B]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [G.IsContinuous K J]
    (M : B) (P : Sheaf J B) (Q : Sheaf K B)
    (qP : (Functor.const Cᵒᵖ).obj M ⟶ P.obj)
    (qQ : (Functor.const Dᵒᵖ).obj M ⟶ Q.obj)
    (c : Q ⟶ (G.sheafPushforwardContinuous B K J).obj P)
    (h : qQ ≫ c.hom = Functor.whiskerLeft G.op qP) :
    Functor.whiskerLeft F.op qQ ≫
      ((F.sheafPushforwardContinuous B J K).map c ≫
        (adj.sheafPushforwardContinuous J K).counit.app P).hom = qP := by
  apply NatTrans.ext
  funext V
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.whiskerLeft_app, Functor.sheafPushforwardContinuous_map_hom_app]
  rw [pushforwardAdjunction_counit_app, ← Category.assoc]
  have hh := congr_app h (F.op.obj V)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hh
  erw [hh]
  have hn := qP.naturality (adj.unit.app V.unop).op
  dsimp only [Functor.const_obj_map] at hn
  erw [Category.id_comp] at hn
  exact hn.symm

private theorem constantCoefficientMap_localization (M : Ab.{u + 1})
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (e : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj M ⟶ R)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : WeaklyEtale f) :
    Functor.whiskerLeft (MorphismProperty.Over.map ⊤ hf).op
        (constantCoefficientMap M R e Y) ≫ (localizedCoefficientMap R f hf).hom =
      constantCoefficientMap M R e X := by
  rw [localizedCoefficientMap_eq]
  exact constantMap_localization
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f hf trivial)
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) M
    (condensedRingObj R X) (condensedRingObj R Y)
    (constantCoefficientMap M R e X) (constantCoefficientMap M R e Y)
    (condensedPushforwardHom R f) (constantCoefficientMap_pushforward M R e f)

private theorem coefficientAbIso_fac (A : Type u) [CommRing A] (X : Scheme.{u}) :
    Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))) forgetCRAb ≫
        (coefficientAbIso A X).hom.hom =
      constantCoefficientMap (AddCommGrpCat.of (ULift.{u + 1} A)) (discreteObj A)
        ((constantCommuteCompose (coherentTopology Profinite.{u}) forgetCRAb).inv.app
          (CommRingCat.of (ULift.{u + 1} A))) X := by
  apply NatTrans.ext
  funext V
  change forgetCRAb.map ((toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app V) ≫
    (coefficientAbIso A X).hom.hom.app V = _
  dsimp only [coefficientAbIso, constantCoefficientMap, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app]
  rw [← Category.assoc]
  congr 1
  ext c
  exact forgetConstant_unit (Scheme.ProEt.topology X) A V c

private theorem underlyingConstant_hom_ext (A : Type u) [CommRing A] (X : Scheme.{u})
    {F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (a b : (sheafCompose (Scheme.ProEt.topology X) forgetCRAb).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} A))) ⟶ F)
    (h : Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))) forgetCRAb ≫
          a.hom =
      Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))) forgetCRAb ≫
          b.hom) : a = b := by
  let B := CommRingCat.of (ULift.{u + 1} A)
  let J := Scheme.ProEt.topology X
  let e := (constantCommuteCompose J forgetCRAb).app B
  have hf : toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (forgetCRAb.obj B)) ≫ e.inv.hom =
      Functor.whiskerRight (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj B)) forgetCRAb := by
    change _ ≫ (sheafifyMap J (Functor.constComp X.ProEtᵒᵖ B forgetCRAb).inv ≫
      (sheafifyComposeIso J forgetCRAb _).hom) = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
      sheafComposeIso_hom_fac]
    ext V c
    rfl
  apply (cancel_epi e.inv).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.property
  change (_ ≫ e.inv.hom) ≫ a.hom = (_ ≫ e.inv.hom) ≫ b.hom
  rw [hf]
  exact h

private theorem coefficientAbIso_localization (A : Type u) [CommRing A]
    {Y : Scheme.{u}} (U : Y.ProEt) :
    (sheafCompose (Scheme.ProEt.topology U.left) forgetCRAb).map
        (localConstantIso A U).hom ≫
      (localizationRestriction Ab.{u + 1} U.hom U.prop).map (coefficientAbIso A Y).hom ≫
        localizedCoefficientMap (discreteObj A) U.hom U.prop =
      (coefficientAbIso A U.left).hom := by
  apply underlyingConstant_hom_ext A U.left
  rw [coefficientAbIso_fac]
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  change Functor.whiskerRight (toSheafify (Scheme.ProEt.topology U.left)
      ((Functor.const U.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))) forgetCRAb ≫
        (Functor.whiskerRight (localConstantIso A U).hom.hom forgetCRAb ≫
      Functor.whiskerLeft (MorphismProperty.Over.map ⊤ U.prop).op
        (coefficientAbIso A Y).hom.hom ≫
      (localizedCoefficientMap (discreteObj A) U.hom U.prop).hom) = _
  rw [← Category.assoc]
  have h := (MorphismProperty.Over.map ⊤ U.prop).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{u + 1} (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
  have hw := congrArg (fun t ↦ Functor.whiskerRight t forgetCRAb) h
  change _ = Functor.whiskerLeft (MorphismProperty.Over.map ⊤ U.prop).op
    (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))) forgetCRAb) at hw
  rw [← Functor.whiskerRight_comp]
  erw [hw]
  rw [← Functor.whiskerLeft_comp_assoc]
  exact (congrArg (fun t ↦ Functor.whiskerLeft (MorphismProperty.Over.map ⊤ U.prop).op t ≫
    (localizedCoefficientMap (discreteObj A) U.hom U.prop).hom)
    (coefficientAbIso_fac A Y)).trans
      (constantCoefficientMap_localization _ _ _ U.hom U.prop)

attribute [irreducible] coefficientAbIso

private theorem constantComparison_comp
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    (G : C ⥤ D) (H : D ⥤ E) (L : C ⥤ E)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (I : GrothendieckTopology E)
    [HasWeakSheafify J B] [HasWeakSheafify K B] [HasWeakSheafify I B]
    [∀ P : Cᵒᵖ ⥤ B, G.op.HasPointwiseRightKanExtension P]
    [∀ P : Dᵒᵖ ⥤ B, H.op.HasPointwiseRightKanExtension P]
    [∀ P : Cᵒᵖ ⥤ B, L.op.HasPointwiseRightKanExtension P]
    [G.IsContinuous J K] [H.IsContinuous K I] [L.IsContinuous J I]
    [G.IsCocontinuous J K] [H.IsCocontinuous K I] [L.IsCocontinuous J I]
    (e : G ⋙ H ≅ L) (M : B) :
    ((G.pushforwardContinuousSheafificationCompatibility B J K).hom.app
        ((Functor.const Dᵒᵖ).obj M)).hom ≫
      Functor.whiskerLeft G.op
        (((H.pushforwardContinuousSheafificationCompatibility B K I).hom.app
          ((Functor.const Eᵒᵖ).obj M)).hom) =
    ((L.pushforwardContinuousSheafificationCompatibility B J I).hom.app
        ((Functor.const Eᵒᵖ).obj M)).hom ≫
      Functor.whiskerRight (NatTrans.op e.hom)
        ((constantSheaf I B).obj M).obj := by
  apply sheafify_hom_ext J
    _ _ (((G.sheafPushforwardContinuous B J K).obj
      ((H.sheafPushforwardContinuous B K I).obj ((constantSheaf I B).obj M))).property)
  rw [← Category.assoc]
  erw [G.toSheafify_pullbackSheafificationCompatibility B J K
    ((Functor.const Dᵒᵖ).obj M)]
  rw [← Functor.whiskerLeft_comp]
  erw [H.toSheafify_pullbackSheafificationCompatibility B K I
    ((Functor.const Eᵒᵖ).obj M)]
  rw [← Category.assoc]
  erw [L.toSheafify_pullbackSheafificationCompatibility B J I
    ((Functor.const Eᵒᵖ).obj M)]
  apply NatTrans.ext
  funext V
  have hn := (toSheafify I ((Functor.const Eᵒᵖ).obj M)).naturality (e.hom.app V.unop).op
  dsimp only [Functor.const_obj_map] at hn
  erw [Category.id_comp] at hn
  exact hn

private theorem weaklyEtale_siteArrow {Y : Scheme.{u}} {U V : Y.ProEt} (g : V ⟶ U) :
    WeaklyEtale g.left := by
  have h : WeaklyEtale (g.left ≫ U.hom) := by
    rw [MorphismProperty.Over.w]
    exact V.prop
  exact WeaklyEtale.of_comp g.left U.hom

private def sliceArrow {Y : Scheme.{u}} {U V : Y.ProEt} (g : V ⟶ U) : U.left.ProEt :=
  MorphismProperty.Over.mk ⊤ g.left (weaklyEtale_siteArrow g)

private theorem localConstantIso_restriction (A : Type u) [CommRing A]
    {Y : Scheme.{u}} {U V : Y.ProEt} (g : V ⟶ U)
    (a : ((constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A))).obj.obj (op U)) :
    let R := (constantSheaf (Scheme.ProEt.topology U.left) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A))
    let S := (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A))
    let T := Scheme.ProEt.mk (𝟙 V.left)
    let q := (MorphismProperty.Over.mkIdTerminal _ U.left).from
      ((MorphismProperty.Over.map ⊤ (sliceArrow g).prop).obj T)
    (localConstantIso A (sliceArrow g)).hom.hom.app (op T)
      ((localConstantIso A V).inv.hom.app (op T)
        (S.obj.map (localObjectIso V).op.hom (S.obj.map g.op a))) =
      R.obj.map q.op
        ((localConstantIso A U).inv.hom.app (op (Scheme.ProEt.mk (𝟙 U.left)))
          (S.obj.map (localObjectIso U).op.hom a)) := by
  let B := CommRingCat.of (ULift.{u + 1} A)
  let R := (constantSheaf (Scheme.ProEt.topology U.left) CommRingCat.{u + 1}).obj B
  let S := (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj B
  let T := Scheme.ProEt.mk (𝟙 V.left)
  let G := MorphismProperty.Over.map ⊤ (sliceArrow g).prop
  let H := MorphismProperty.Over.map ⊤ U.prop
  let L := MorphismProperty.Over.map ⊤ V.prop
  have : G.IsContinuous (Scheme.ProEt.topology V.left)
      (Scheme.ProEt.topology U.left) := Scheme.ProEt.isContinuous_overMap (sliceArrow g).prop
  have : G.IsCocontinuous (Scheme.ProEt.topology V.left)
      (Scheme.ProEt.topology U.left) := Scheme.ProEt.isCocontinuous_overMap (sliceArrow g).prop
  have : H.IsContinuous (Scheme.ProEt.topology U.left)
      (Scheme.ProEt.topology Y) := Scheme.ProEt.isContinuous_overMap U.prop
  have : H.IsCocontinuous (Scheme.ProEt.topology U.left)
      (Scheme.ProEt.topology Y) := Scheme.ProEt.isCocontinuous_overMap U.prop
  have : L.IsContinuous (Scheme.ProEt.topology V.left)
      (Scheme.ProEt.topology Y) := Scheme.ProEt.isContinuous_overMap V.prop
  have : L.IsCocontinuous (Scheme.ProEt.topology V.left)
      (Scheme.ProEt.topology Y) := Scheme.ProEt.isCocontinuous_overMap V.prop
  let q := (MorphismProperty.Over.mkIdTerminal _ U.left).from (G.obj T)
  let e : G ⋙ H ≅ L :=
    (MorphismProperty.Over.mapComp (Q := ⊤) (sliceArrow g).prop U.prop V.hom
      (MorphismProperty.Over.w g).symm).symm
  let b := (localConstantIso A V).inv.hom.app (op T)
    (S.obj.map (localObjectIso V).op.hom (S.obj.map g.op a))
  let r := (localConstantIso A U).inv.hom.app (op (Scheme.ProEt.mk (𝟙 U.left)))
    (S.obj.map (localObjectIso U).op.hom a)
  have hb : (localConstantIso A V).hom.hom.app (op T) b =
      S.obj.map (localObjectIso V).op.hom (S.obj.map g.op a) := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun t ↦ t.hom.app (op T)) (localConstantIso A V).inv_hom_id) _
  have hr : (localConstantIso A U).hom.hom.app (op (Scheme.ProEt.mk (𝟙 U.left))) r =
      S.obj.map (localObjectIso U).op.hom a := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun t ↦ t.hom.app (op (Scheme.ProEt.mk (𝟙 U.left))))
        (localConstantIso A U).inv_hom_id) _
  have hc := ConcreteCategory.congr_hom (congr_app
    (constantComparison_comp G H L (Scheme.ProEt.topology V.left)
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology Y) e B) (op T)) b
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ConcreteCategory.comp_apply] at hc
  change (localConstantIso A U).hom.hom.app (op (G.obj T))
    ((localConstantIso A (sliceArrow g)).hom.hom.app (op T) b) =
      S.obj.map (e.hom.app T).op ((localConstantIso A V).hom.hom.app (op T) b) at hc
  rw [hb] at hc
  have hn := ConcreteCategory.congr_hom ((localConstantIso A U).hom.hom.naturality q.op) r
  simp only [ConcreteCategory.comp_apply] at hn
  change (localConstantIso A U).hom.hom.app (op (G.obj T)) (R.obj.map q.op r) =
    S.obj.map (H.map q).op
      ((localConstantIso A U).hom.hom.app (op (Scheme.ProEt.mk (𝟙 U.left))) r) at hn
  rw [hr] at hn
  have hq : q.left = g.left := by
    have h := MorphismProperty.Over.w q
    change q.left ≫ 𝟙 U.left = 𝟙 V.left ≫ g.left at h
    exact (Category.comp_id q.left).symm.trans (h.trans (Category.id_comp g.left))
  have hm : e.hom.app T ≫ (localObjectIso V).hom ≫ g =
      H.map q ≫ (localObjectIso U).hom := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 V.left ≫ 𝟙 V.left ≫ g.left = q.left ≫ 𝟙 U.left
    exact (Category.id_comp (𝟙 V.left ≫ g.left)).trans
      ((Category.id_comp g.left).trans (hq.symm.trans (Category.comp_id q.left).symm))
  apply (ConcreteCategory.bijective_of_isIso
    ((localConstantIso A U).hom.hom.app (op (G.obj T)))).1
  change (localConstantIso A U).hom.hom.app (op (G.obj T))
      ((localConstantIso A (sliceArrow g)).hom.hom.app (op T) b) =
    (localConstantIso A U).hom.hom.app (op (G.obj T)) (R.obj.map q.op r)
  rw [hc, hn]
  change S.obj.map (e.hom.app T).op
    (S.obj.map (localObjectIso V).hom.op (S.obj.map g.op a)) =
      S.obj.map (H.map q).op (S.obj.map (localObjectIso U).hom.op a)
  have hh := congrArg (fun k ↦ S.obj.map k.op a) hm
  simp only [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply] at hh
  exact hh

attribute [irreducible] localConstantIso

private def schemeCoordinate (A : Type u) [CommRing A] {Y : Scheme.{u}} (U : Y.ProEt)
    (a : ((constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A))).obj.obj (op U)) :
    𝟙_ (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1}) ⟶
      condensedRingObj (discreteObj A) U.left :=
  (unitSectionEquiv (Scheme.ProEt.topology U.left)
    (MorphismProperty.Over.mkIdTerminal _ U.left) _).symm
      ((localConstantIso A U).inv.hom.app (op (Scheme.ProEt.mk (𝟙 U.left)))
        (((constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} A))).obj.map (localObjectIso U).op.hom a)) ≫
    (coefficientAbIso A U.left).hom

private theorem monoidalIso_unit_map
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) [F.LaxMonoidal] [G.LaxMonoidal] (e : F ≅ G)
    [NatTrans.IsMonoidal e.hom] {Y : C} {Z : D} (t : 𝟙_ C ⟶ Y) (k : F.obj Y ⟶ Z) :
    Functor.LaxMonoidal.ε F ≫ F.map t ≫ k =
      Functor.LaxMonoidal.ε G ≫ G.map t ≫ e.inv.app Y ≫ k := by
  rw [reassoc_of% e.inv.naturality t, NatTrans.IsMonoidal.unit_assoc]

private theorem pullbackUnitSection_localization
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : WeaklyEtale f)
    (t : 𝟙_ (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) ⟶ condensedRingObj R Y) :
    Functor.LaxMonoidal.ε (upperStar Ab.{u + 1} f) ≫
        (upperStar Ab.{u + 1} f).map t ≫ condensedPullbackHom R f =
      Functor.LaxMonoidal.ε ((MorphismProperty.Over.map ⊤ hf).sheafPushforwardContinuous
        Ab.{u + 1} (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)) ≫
        (localizationRestriction Ab.{u + 1} f hf).map t ≫
          localizedCoefficientMap R f hf := by
  exact monoidalIso_unit_map _ _ (upperStarIsoSheafPushforward Ab.{u + 1} f hf)
    t (condensedPullbackHom R f)

private theorem schemeCoordinate_naturality (A : Type u) [CommRing A]
    {Y : Scheme.{u}} {U V : Y.ProEt} (g : V ⟶ U)
    (a : ((constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A))).obj.obj (op U)) :
    Functor.LaxMonoidal.ε (upperStar Ab.{u + 1} g.left) ≫
        (upperStar Ab.{u + 1} g.left).map (schemeCoordinate A U a) ≫
          condensedPullbackHom (discreteObj A) g.left =
      schemeCoordinate A V
        (((constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} A))).obj.map g.op a) := by
  let B := CommRingCat.of (ULift.{u + 1} A)
  let R := (constantSheaf (Scheme.ProEt.topology U.left) CommRingCat.{u + 1}).obj B
  let S := (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj B
  let T := Scheme.ProEt.mk (𝟙 V.left)
  let G := MorphismProperty.Over.map ⊤ (sliceArrow g).prop
  have : G.IsContinuous (Scheme.ProEt.topology V.left)
      (Scheme.ProEt.topology U.left) := Scheme.ProEt.isContinuous_overMap (sliceArrow g).prop
  let q := (MorphismProperty.Over.mkIdTerminal _ U.left).from (G.obj T)
  let r := (localConstantIso A U).inv.hom.app (op (Scheme.ProEt.mk (𝟙 U.left)))
    (S.obj.map (localObjectIso U).op.hom a)
  let b := (localConstantIso A V).inv.hom.app (op T)
    (S.obj.map (localObjectIso V).op.hom (S.obj.map g.op a))
  have ht : R.obj.map q.op r =
      (localConstantIso A (sliceArrow g)).hom.hom.app (op T) b :=
    (localConstantIso_restriction A g a).symm
  erw [pullbackUnitSection_localization (discreteObj A) g.left (weaklyEtale_siteArrow g)]
  let K := G.sheafPushforwardContinuous Ab.{u + 1}
    (Scheme.ProEt.topology V.left) (Scheme.ProEt.topology U.left)
  let t := (unitSectionEquiv (Scheme.ProEt.topology U.left)
    (MorphismProperty.Over.mkIdTerminal _ U.left)
    ((sheafCompose (Scheme.ProEt.topology U.left) forgetCRAb).obj R)).symm r
  change Functor.LaxMonoidal.ε K ≫ K.map (t ≫ (coefficientAbIso A U.left).hom) ≫
    localizedCoefficientMap (discreteObj A) g.left (sliceArrow g).prop = _
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (Functor.LaxMonoidal.ε K) (K.map t)]
  erw [unitSectionEquiv_restriction G (Scheme.ProEt.topology V.left)
    (Scheme.ProEt.topology U.left) (MorphismProperty.Over.mkIdTerminal _ V.left)
    (MorphismProperty.Over.mkIdTerminal _ U.left)
    ((sheafCompose (Scheme.ProEt.topology U.left) forgetCRAb).obj R) r]
  erw [ht]
  erw [← unitSectionEquiv_symm_naturality (Scheme.ProEt.topology V.left)
    (MorphismProperty.Over.mkIdTerminal _ V.left)
    ((sheafCompose (Scheme.ProEt.topology V.left) forgetCRAb).map
      (localConstantIso A (sliceArrow g)).hom) b]
  simp only [Category.assoc]
  exact congrArg (fun k ↦ (unitSectionEquiv (Scheme.ProEt.topology V.left)
    (MorphismProperty.Over.mkIdTerminal _ V.left)
    ((sheafCompose (Scheme.ProEt.topology V.left) forgetCRAb).obj
      ((constantSheaf (Scheme.ProEt.topology V.left) CommRingCat.{u + 1}).obj B))).symm b ≫ k)
    (coefficientAbIso_localization A (sliceArrow g))

private theorem coordinateEquiv_eq_schemeCoordinate (A : Type u) [CommRing A]
    {Y : Scheme.{u}} (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y)
    (s : ((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
      CommRingCat.{u + 1}).obj (CommRingCat.of (ULift.{u + 1} A))).obj.obj (op U)) :
    coordinateEquiv A U s = schemeCoordinate A (AsSmall.down.obj U)
      ((smallConstantIso A Y).hom.hom.app (op U) s) := by
  let W := AsSmall.down.obj U
  let B := CommRingCat.of (ULift.{u + 1} A)
  let R := (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj B
  let T := Scheme.ProEt.mk (𝟙 W.left)
  change (𝟙 _ ≫ (unitSectionEquiv (Scheme.ProEt.topology W.left)
    (MorphismProperty.Over.mkIdTerminal _ W.left)
      ((sheafCompose (Scheme.ProEt.topology W.left) forgetCRAb).obj
        ((constantSheaf (Scheme.ProEt.topology W.left) CommRingCat.{u + 1}).obj B))).symm
      ((localConstantIso A W).inv.hom.app (op T)
        (R.obj.map (localObjectIso W).op.hom
          ((smallConstantIso A Y).hom.hom.app (op U) s))) ≫
        (coefficientAbIso A W.left).hom) = _
  rw [Category.id_comp]
  rfl

attribute [irreducible] coordinateEquiv schemeCoordinate

private theorem coordinateEquiv_naturality (A : Type u) [CommRing A]
    {Y : Scheme.{u}} {U V : Scheme.coefficientProEtaleSiteModel.{u, u} Y} (g : V ⟶ U)
    (s : ((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
      CommRingCat.{u + 1}).obj (CommRingCat.of (ULift.{u + 1} A))).obj.obj (op U)) :
    Functor.LaxMonoidal.ε (upperStar Ab.{u + 1} (AsSmall.down.map g).left) ≫
        (upperStar Ab.{u + 1} (AsSmall.down.map g).left).map (coordinateEquiv A U s) ≫
          condensedPullbackHom (discreteObj A) (AsSmall.down.map g).left =
      coordinateEquiv A V
        (((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
          CommRingCat.{u + 1}).obj (CommRingCat.of (ULift.{u + 1} A))).obj.map g.op s) := by
  rw [coordinateEquiv_eq_schemeCoordinate A U s]
  rw [schemeCoordinate_naturality A (AsSmall.down.map g)]
  rw [coordinateEquiv_eq_schemeCoordinate A V]
  congr 1
  exact (ConcreteCategory.congr_hom ((smallConstantIso A Y).hom.hom.naturality g.op) s).symm

attribute [irreducible] constantScalarSection

/-- A global coefficient section on U.left has a coordinate on the equivalent small site.
If that coordinate restricts to a constant scalar, its inverse image is the point
constant section. This compares sections only; no module morphism, covering sieve,
finite index set or matrix occurs in the statement.

Source: Stacks, Tags 03CY and 00YV; `constantSchemeIso` and weakly-etale localization.
(auxiliary; not a blueprint node).

Proof: the monoidal comparison `constantSchemeIso`, composed with the comparisons
forgetting commutative rings to abelian groups, identifies x with a section of the
constant ring sheaf on U.left. Weakly-etale localization identifies terminal sections
on U.left with sections on U in Y.ProEt; AsSmall transports the same section to the
specified small site, giving s. These identifications commute with restriction.
The hypothesis on c therefore says that the restriction of x is the constant c
section. The adjunction defining `upperStar` identifies restriction with inverse
image followed by the canonical coefficient comparison. The constant-sheaf
adjunction defining `discretePointScalarSection` sends c to that same constant
section. Its transported unit supplies the epsilon factors in the formula.
This proves the asserted equality, including for the zero ring and empty schemes. -/
theorem discrete_section_coordinates
    (A : Type u) [CommRing A] {Y : Scheme.{u}}
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y)
    (x : 𝟙_ (Sheaf (Scheme.ProEt.topology (AsSmall.down.obj U).left) Ab.{u + 1}) ⟶
      condensedRingObj (discreteObj A) (AsSmall.down.obj U).left) :
    ∃ s : ((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
        CommRingCat.{u + 1}).obj (CommRingCat.of (ULift.{u + 1} A))).obj.obj (op U),
      ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U)
        (c : ULift.{u + 1} A),
        (toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
          ((Functor.const (Scheme.coefficientProEtaleSiteModel.{u, u} Y)ᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} A)))).app (op V) c =
          ((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
            CommRingCat.{u + 1}).obj (CommRingCat.of (ULift.{u + 1} A))).obj.map g.op s →
        Functor.LaxMonoidal.ε (upperStar Ab.{u + 1} (AsSmall.down.map g).left) ≫
            (upperStar Ab.{u + 1} (AsSmall.down.map g).left).map x ≫
            condensedPullbackHom (discreteObj A) (AsSmall.down.map g).left =
          Functor.LaxMonoidal.ε (upperStarFromPoint (AsSmall.down.obj V).left) ≫
            (upperStarFromPoint (AsSmall.down.obj V).left).map
              (discretePointScalarSection A c) := by
  let s := (coordinateEquiv A U).symm x
  have hx : coordinateEquiv A U s = x := (coordinateEquiv A U).apply_symm_apply x
  refine ⟨s, ?_⟩
  intro V g c hc
  have h₁ := coordinateEquiv_naturality A g s
  have h₂ := congrArg (coordinateEquiv A V) hc
  have h₃ := coordinateEquiv_unit A V c
  have h₄ := constantScalarSection_point A (AsSmall.down.obj V).left c
  exact (congrArg (fun z ↦
    Functor.LaxMonoidal.ε (upperStar Ab.{u + 1} (AsSmall.down.map g).left) ≫
      (upperStar Ab.{u + 1} (AsSmall.down.map g).left).map z ≫
        condensedPullbackHom (discreteObj A) (AsSmall.down.map g).left) hx.symm).trans
    (h₁.trans (h₂.symm.trans (h₃.trans h₄)))

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
