/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.AffineModuleComplexRepresentative
import WeilConjectures.AlgebraicGeometry.AffineKFlatPullbackChartComparison
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # A module-complex model for affine derived pullback

Source: Stacks Project, Tag 08DW(2), using Tag 06Z0 and Tag 08DV.
(blueprint: lem-pc-affine-derived-pullback-module-model).
-/

@[expose] public section

universe u w wS

open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Affine derived pullback has a module-complex representative on the target spectrum.
Source: Stacks Project, Tag 08DW(2), Tag 06Z0 and Tag 08DV.
Proof: use the canonical spectrum presentations of X and Y and the induced ring map.
The affine derived equivalence represents E by termwise tilde of a module complex M.
Choose a K-flat resolution P of M. The affine pullback comparison identifies its
pullback with termwise tilde of the base-changed complex B tensor P. The tilde complex of P,
restricted along Y to its spectrum, represents E.
The base-changed complex along f.appTop.hom represents its pullback after termwise tilde
and exact restriction along X to its spectrum. Transport the natural comparisons
through the two canonical spectrum presentations. No flatness of f or boundedness of E is
needed; the zero ring is allowed.
(blueprint: lem-pc-affine-derived-pullback-module-model). -/
theorem exists_affine_derivedPullback_module_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))]
    (E : schemeDerivedCategory Y) (hE : schemeDerivedQCohProperty Y E) :
    ∃ P : CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(Y, ⊤)) (.up ℤ)).kFlat P ∧
      Nonempty (E ≅ DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings Y.toRingedSpace))
            (Scheme.Modules.restrictFunctor Y.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor Y.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(Y, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace))
                (tilde.functor Γ(Y, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj P))) ∧
      Nonempty ((derivedPullback f).obj E ≅
        (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings X.toRingedSpace))
            (Scheme.Modules.restrictFunctor X.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor X.toSpecΓ).Additive; infer_instance)
          (by change PreservesFiniteLimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
              infer_instance)
          (by change PreservesFiniteColimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
              infer_instance)).obj
            (DerivedCategory.Q.obj
              ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
                (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
                  SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
                  (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                  ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
                    (ModuleCat.extendScalars f.appTop.hom)
                    (Functor.preservesZeroMorphisms_of_isLeftAdjoint _) (.up ℤ)).obj P)))) := by
  classical
  obtain ⟨M, ⟨e⟩⟩ := exists_affine_module_complex_representative Y E hE
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} Γ(Y, ⊤)))).reduced
  let P := Λ.resolutionFunctor.obj M
  let s : P ⟶ M := (Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le).app M
  have hs : QuasiIso s := by dsimp [s, P]; infer_instance
  have hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(Y, ⊤)) (.up ℤ)).kFlat P :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le M
  let T : ModuleCat.{u} Γ(Y, ⊤) ⥤
      SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace) :=
    tilde.functor Γ(Y, ⊤)
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := Γ(Y, ⊤)) f g
  let R := moduleSpecΓFunctor (R := Γ(Y, ⊤))
  have adj : T ⊣ R := tilde.adjunction
  let : T.IsLeftAdjoint := adj.isLeftAdjoint
  let : PreservesFiniteColimits T := inferInstance
  let : T.PreservesMonomorphisms := ⟨by
    intro M N f hf
    let : Mono f := hf
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U a b h
    apply Subtype.ext
    funext x
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N)
      f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)
    exact congrArg (fun z ↦ z.val x) h⟩
  let : T.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels T
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  let RY : SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
    Scheme.Modules.restrictFunctor Y.toSpecΓ
  let : RY.Additive := by
    change (Scheme.Modules.restrictFunctor Y.toSpecΓ).Additive
    infer_instance
  let : PreservesFiniteLimits RY := by
    change PreservesFiniteLimits (Scheme.Modules.restrictFunctor Y.toSpecΓ)
    infer_instance
  let : PreservesFiniteColimits RY := by
    change PreservesFiniteColimits (Scheme.Modules.restrictFunctor Y.toSpecΓ)
    infer_instance
  let F := T ⋙ RY
  let FC := F.mapHomologicalComplex (.up ℤ)
  let : QuasiIso s := hs
  have : QuasiIso (FC.map s) := inferInstance
  have : IsIso (DerivedCategory.Q.map (FC.map s)) := inferInstance
  let eP := e ≪≫ (asIso (DerivedCategory.Q.map (FC.map s))).symm
  obtain ⟨c⟩ := affine_kFlat_pullback_chart_comparison f P hP
  refine ⟨P, hP, ⟨eP⟩, ?_⟩
  exact ⟨(derivedPullback f).mapIso eP ≪≫ c⟩

end AlgebraicGeometry
