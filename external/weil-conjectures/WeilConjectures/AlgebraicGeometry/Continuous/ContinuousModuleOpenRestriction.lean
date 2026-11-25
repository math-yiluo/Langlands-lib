/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModelOpenClosedBasic
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModelOpenClosedBasic

set_option linter.privateModule false

/-!
# Continuous-coefficient restriction on the localized pro-etale site

Source: Stacks Project, Tags 09BN, 00XZ and 03D2
(blueprint: lem-weil-pbc-continuous-module-open-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
private def continuousRestriction {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing X T) ⥤
      SheafOfModules.{u + 1} (latticeModuleRing U.left T) := by
  let G : U.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ U.prop
  let : G.IsContinuous (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap U.prop
  exact SheafOfModules.pushforward (F := G)
    (J := Scheme.ProEt.topology U.left) (K := Scheme.ProEt.topology X)
    (S := latticeModuleRing U.left T) (R := latticeModuleRing X T)
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩

set_option backward.isDefEq.respectTransparency false in
private def restrictionToSlice {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    continuousRestriction U T ⋙ openSliceModules U T ≅
      SheafOfModules.overFunctor (latticeModuleRing X T) U := by
  let G : U.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ U.prop
  let : G.IsContinuous (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap U.prop
  let := Scheme.ProEt.sliceDense X U
  let : (Scheme.ProEt.sliceEquiv X U).functor.IsContinuous
      ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left) := inferInstance
  let H := (Scheme.ProEt.sliceEquiv X U).functor ⋙ G
  let : H.IsContinuous ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology X) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology U.left) _
  let e : H ≅ Over.forget U := NatIso.ofComponents (fun V ↦
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ V.left.hom = V.hom.left ≫ U.hom
      simp only [Category.id_comp, MorphismProperty.Over.w])) (by
        intro V W f
        apply MorphismProperty.Over.Hom.ext
        change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
        simp)
  let φ : (latticeModuleRing X T).over U ⟶
      (H.sheafPushforwardContinuous RingCat.{u + 1}
        ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology X)).obj
          (latticeModuleRing X T) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  let ψ : latticeModuleRing U.left T ⟶
      (G.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X)).obj
          (latticeModuleRing X T) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  let χ : (latticeModuleRing X T).over U ⟶
      ((Scheme.ProEt.sliceEquiv X U).functor.sheafPushforwardContinuous RingCat.{u + 1}
        ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left)).obj
          (latticeModuleRing U.left T) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  refine (SheafOfModules.pushforwardComp χ ψ) ≪≫ ?_
  refine (SheafOfModules.pushforwardCongr ?_) ≪≫
    SheafOfModules.pushforwardCongr₂ φ e.symm (by ext V s; rfl)
  ext V s
  rfl

end AlgebraicGeometry.ProEtale
