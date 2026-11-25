/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement

/-! # Scalar extension and restriction to a pro-etale slice

## References

* Stacks Project, Modules on Sites, Tag 03EL
* Cohomology on Sites, Tags 06YS, 0G7E and 06YY
* Stacks 00XZ, 03EL and 03CZ
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Literal restriction of module sheaves to a pro-etale site object. -/
abbrev proEtaleSliceModules {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcModules X R ⥤ pbcModules U.left
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) :=
  letI : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  SheafOfModules.pushforward (F := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop)
    (J := ProEt.topology U.left) (K := ProEt.topology X) (𝟙 _)

private theorem exact_moduleRestriction
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [F.IsCocontinuous J K] [F.IsLeftAdjoint]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) [IsIso φ] :
    (SheafOfModules.pushforward.{u} φ).Additive ∧
      PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj F.op)
    infer_instance
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) :=
    preservesFiniteLimits_of_reflects_of_preserves _ T
  have : (SheafOfModules.pushforward.{u} φ).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso φ
  refine ⟨?_, inferInstance, inferInstance⟩
  constructor
  intro M N f g
  apply SheafOfModules.hom_ext
  ext V m
  rfl

/-- Exactness of literal restriction, including nonnoetherian U. -/
theorem proEtaleSliceModules_exact {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleSliceModules U R).Additive ∧ PreservesFiniteLimits (proEtaleSliceModules U R) ∧
      PreservesFiniteColimits (proEtaleSliceModules U R) := by
  let G := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop
  let : G.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  let : G.IsCocontinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap U.prop
  let : G.IsLeftAdjoint :=
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial).isLeftAdjoint
  exact exact_moduleRestriction (F := G) (𝟙 _)

end AlgebraicGeometry.Scheme
