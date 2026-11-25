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
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.Algebra.Homology.KFlatPullback

/-! # Affine pullback comparison through spectrum charts

Source: Stacks Project, Tags 06Z0 and 08DW.
(blueprint: lem-pc-affine-kflat-pullback-chart-comparison).
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

private theorem tensorPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive := by
  let : (Scheme.Modules.tensorPullback f).IsLeftAdjoint :=
    ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction f⟩
  exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)

private noncomputable def tensorPullbackRestrictIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    Scheme.Modules.tensorPullback f ≅ Scheme.Modules.restrictFunctor f :=
  (Scheme.Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
    (Scheme.Modules.restrictAdjunction f)

private theorem isKFlat_of_iso {X : Scheme.{u}}
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (e : K ≅ L) (hK : CochainComplex.IsKFlatTensor (R := X.sheaf) K) :
    CochainComplex.IsKFlatTensor (R := X.sheaf) L := by
  let := SheafOfModules.monoidalCategory X.sheaf
  intro F hF i
  exact (hK F hF i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e)

/-- Transport the affine derived pullback calculation through canonical spectrum charts.
Source: Stacks Project, Tag 08DW(2), using Tag 08DV.
Proof: naturality of toSpecΓ identifies f followed by Y.toSpecΓ with X.toSpecΓ
followed by Spec.map f.appTop. Restriction along these scheme isomorphisms is exact.
Termwise tensor pullback commutes with these restrictions. Tilde of the K-flat module
complex is K-flat; the derived-pullback counits therefore identify both functors with
these termwise calculations. Apply derivedPullback_tilde_iso with the identity resolution
of P and transport its comparison through the chart isomorphisms. Uniqueness of the
localization lift of the exact restriction gives the comparison even when the target
spectrum has an independent localization universe. No quasi-coherence condition on an
arbitrary derived object, or choice of a representative for it, occurs in this statement.
(blueprint: lem-pc-affine-kflat-pullback-chart-comparison). -/
theorem affine_kFlat_pullback_chart_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))]
    (P : CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(Y, ⊤)) (.up ℤ)).kFlat P) :
    Nonempty ((derivedPullback f).obj
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings Y.toRingedSpace))
            (Scheme.Modules.restrictFunctor Y.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor Y.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(Y, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace))
                (tilde.functor Γ(Y, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj P))) ≅
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
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let TY := tilde.functor Γ(Y, ⊤)
  let TX := tilde.functor Γ(X, ⊤)
  have : TY.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : TX.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let RY := Scheme.Modules.restrictFunctor Y.toSpecΓ
  let RX : SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤ B :=
    Scheme.Modules.restrictFunctor X.toSpecΓ
  have : RX.Additive := by
    change (Scheme.Modules.restrictFunctor X.toSpecΓ).Additive
    infer_instance
  have : PreservesFiniteLimits RX := by
    change PreservesFiniteLimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
    infer_instance
  have : PreservesFiniteColimits RX := by
    change PreservesFiniteColimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
    infer_instance
  let S := Spec.map f.appTop
  let E := Scheme.Modules.tensorPullback f
  have : E.Additive := tensorPullback_additive f
  have : (Scheme.Modules.tensorPullback S).Additive := tensorPullback_additive S
  have : (Scheme.Modules.tensorPullback Y.toSpecΓ).Additive :=
    tensorPullback_additive Y.toSpecΓ
  have : (Scheme.Modules.tensorPullback X.toSpecΓ).Additive :=
    tensorPullback_additive X.toSpecΓ
  let K := (TY.mapHomologicalComplex (.up ℤ)).obj P
  let C := (RY.mapHomologicalComplex (.up ℤ)).obj K
  have hK : CochainComplex.IsKFlatTensor (R := (Spec Γ(Y, ⊤)).sheaf) K := by
    apply isKFlat_tilde Γ(Y, ⊤) P
    intro F hF
    have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)).mp
        ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF)).2
  have hC : CochainComplex.IsKFlatTensor (R := Y.sheaf) C := by
    have h := CochainComplex.isKFlat_pullback Y.toSpecΓ.base Y.sheaf
      (Spec Γ(Y, ⊤)).sheaf ⟨Y.toSpecΓ.c⟩ K hK
    apply isKFlat_of_iso
      ((NatIso.mapHomologicalComplex (tensorPullbackRestrictIso Y.toSpecΓ) (.up ℤ)).app K)
    convert h using 1
    rfl
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hflat⟩ :=
    (derivedPullback_spec f)
  have hEq : F = E := CategoryTheory.Functor.ext hF (fun _ _ a ↦ hFmap a)
  subst F
  have : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj C)) := hflat C hC
  let e : (derivedPullback f).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj C) :=
    (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso A).app C).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj C)) ≪≫
      DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app C) ≪≫
      (DerivedCategory.quotientCompQhIso B).app _
  let square : RY ⋙ E ≅ Scheme.Modules.tensorPullback S ⋙ RX :=
    Functor.isoWhiskerRight (tensorPullbackRestrictIso Y.toSpecΓ).symm E ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp f Y.toSpecΓ).some.symm ≪≫
      eqToIso (congrArg Scheme.Modules.tensorPullback (Scheme.toSpecΓ_naturality f)) ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp X.toSpecΓ S).some ≪≫
      Functor.isoWhiskerLeft _ (tensorPullbackRestrictIso X.toSpecΓ)
  obtain ⟨θ, _⟩ := Scheme.Modules.exists_tensorPullback_tilde_iso f.appTop
  let comparison : (TY ⋙ RY) ⋙ E ≅
      (ModuleCat.extendScalars f.appTop.hom ⋙ TX) ⋙ RX :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft TY square ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight θ RX
  let : (ModuleCat.extendScalars f.appTop.hom).IsLeftAdjoint :=
    ⟨_, ⟨ModuleCat.extendRestrictScalarsAdj f.appTop.hom⟩⟩
  have : (ModuleCat.extendScalars f.appTop.hom).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  let δ := (NatIso.mapHomologicalComplex comparison (.up ℤ)).app P
  refine ⟨e ≪≫ DerivedCategory.Q.mapIso δ ≪≫ ?_⟩
  exact ((Functor.mapDerivedCategoryFactors.{wS, w} RX).app
    ((TX.mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars f.appTop.hom).mapHomologicalComplex (.up ℤ)).obj P))).symm

end AlgebraicGeometry
