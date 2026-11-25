/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! Canonical derived pullback comparison: Stacks Project, Tag 0D5S. -/

@[expose] public section

universe u₁ w₁
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

private theorem tensorPullback_kFlat {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    [(Scheme.Modules.tensorPullback f).Additive]
    (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Y.sheaf) P) :
    CochainComplex.IsKFlatTensor (R := X.sheaf)
      (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have h := CochainComplex.isKFlat_pullback f.base X.sheaf Y.sheaf ⟨f.c⟩ P hP
  convert h using 1
  rfl

/-- The canonical lift of the composite tensor counit is invertible.
Source: Stacks Project, Cohomology, Tag 0D5S.
(blueprint: lem-pc-derived-pullback-comparison-is-iso).
Proof: choose a K-flat resolution P → E using Tag 06YS. Pullback of P along g is
K-flat by Tag 06YC. The supplied K-flat counit condition makes ε g at P and ε f
at g*P invertible. The underived comparison is an isomorphism. The defining
factorization of the left-derived lift therefore makes its component at Q(P)
invertible, since ε (f ≫ g) at P is invertible too. The localization of the
resolution is an isomorphism Q(P) ≅ Q(E), so naturality gives invertibility at
Q(E). Every derived object is isomorphic to an object in the image of Q; hence
all components are invertible and the natural transformation is invertible.
This uses no flatness assumption on the scheme morphisms. -/
theorem isIso_derivedPullbackCompositionLift
    [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    (a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
      (ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))
      (hL : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        (derivedPullback f).IsLeftDerivedFunctor (ε f)
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    (hK : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y)
      (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ),
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
        IsIso ((ε f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))
    {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso ((derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
            (derivedPullback g ⋙ derivedPullback f)
            ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh
                (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))))) := by
  let β := ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh
                (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))))
  let τ := (derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
            (derivedPullback g ⋙ derivedPullback f) β
  change IsIso τ
  have hflat (P : CochainComplex
      (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) ℤ)
      (hP : CochainComplex.IsKFlatTensor (R := Z.sheaf) P) :
      IsIso (τ.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) := by
    have hg := hK g P hP
    have hfg := hK (f ≫ g) P hP
    have hf := hK f
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (tensorPullback_kFlat g P hP)
    have hf' : IsIso ((ε f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient
            (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ)).obj P))) := by
      rw [Functor.mapHomotopyCategory_obj]
      exact hf
    have fac := (derivedPullback (f ≫ g)).leftDerived_fac_app (ε (f ≫ g))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
      (derivedPullback g ⋙ derivedPullback f) β
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)
    have : IsIso (τ.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
          (ε (f ≫ g)).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
      rw [show τ.app _ ≫ _ = _ from fac]
      dsimp only [β, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      set_option synthInstance.maxSize 512 in infer_instance
    exact IsIso.of_isIso_comp_right _
      ((ε (f ≫ g)).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
  apply (NatTrans.isIso_iff_isIso_app τ).2
  intro K
  let Q := DerivedCategory.Qh
    (C := SheafOfModules.{u₁} (moduleRings Z.toRingedSpace))
  apply (NatTrans.isIso_app_iff_of_iso τ (Q.objObjPreimageIso K)).1
  obtain ⟨G, hG⟩ := HomotopyCategory.quotient_obj_surjective (Q.objPreimage K)
  rw [← hG]
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Z.sheaf) G
  have hsq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  have := Localization.inverts Q
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ hsq
  apply (NatTrans.isIso_app_iff_of_iso τ
    (asIso (Q.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)))).1
  exact hflat P hP

end AlgebraicGeometry
