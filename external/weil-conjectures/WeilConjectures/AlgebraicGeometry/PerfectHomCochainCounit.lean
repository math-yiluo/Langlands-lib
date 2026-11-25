/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # The fixed composition counits on cochain complexes
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-perfect-hom-cochain-counit). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The additive structure already selected in the fixed composition theorem. 
(blueprint: lem-pc-perfect-hom-cochain-counit)
-/
abbrev perfectHomTensorAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  Classical.choose exists_derivedPullbackComposition f

/-- Termwise tensor pullback with the additive structure used by composition. 
(blueprint: lem-pc-perfect-hom-cochain-counit)
-/
noncomputable abbrev perfectHomTensorComplex {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  let := perfectHomTensorAdditive f
  (Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)

/-- The original fixed counit; this is the witness already used by perfectHomComposition. 
(blueprint: lem-pc-perfect-hom-cochain-counit)
-/
noncomputable abbrev perfectHomTensorCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (letI := perfectHomTensorAdditive f
       (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)) ⋙ DerivedCategory.Qh.{w}
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choose (Classical.choose_spec exists_derivedPullbackComposition) f

private theorem tensorDerivedCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ (_ : (Scheme.Modules.tensorPullback f).Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
        (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))),
      (derivedPullback f).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) ∧
      ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      derivedPullback_spec f
  have h : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  exact ⟨hEadd, ε, hL, hK⟩

/-- The fixed composition counit is invertible at any K-flat complex.
Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-pc-perfect-hom-cochain-counit).
Proof: the defining derived-pullback counit is invertible on K-flat models.
Uniqueness of left derived functors identifies it with the counit selected for
composition. Its comparison is an isomorphism, so the fixed counit is invertible
on the same models. -/
theorem perfectHomTensorCounit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Y.sheaf) P) :
    IsIso ((perfectHomTensorCounit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  let := perfectHomTensorAdditive f
  have hL : (derivedPullback f).IsLeftDerivedFunctor (perfectHomTensorCounit f)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) :=
    Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)) f
  obtain ⟨a, ε, hε, hK⟩ := tensorDerivedCounit f
  let := hL
  let := hε
  let τ := (derivedPullback f).leftDerivedLift (perfectHomTensorCounit f)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (derivedPullback f) ε
  have hτ : IsIso τ :=
    ((derivedPullback f).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      (perfectHomTensorCounit f) (HomotopyCategory.quasiIso _ (.up ℤ))
      (derivedPullback f) ε).mp hε
  have he := (derivedPullback f).leftDerived_fac_app (perfectHomTensorCounit f)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (derivedPullback f) ε
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hK P hP
  have hfixed : IsIso ((perfectHomTensorCounit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
    have : IsIso (τ.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
          (perfectHomTensorCounit f).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
      change IsIso (((derivedPullback f).leftDerivedLift (perfectHomTensorCounit f)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (derivedPullback f) ε).app _ ≫ _)
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left (τ.app _) _
  exact hfixed

/-- The fixed termwise tensor pullback on homotopy categories. 
(blueprint: lem-pc-perfect-hom-cochain-counit)
-/
noncomputable abbrev perfectHomTensorHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  let := perfectHomTensorAdditive f
  (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)

/-- The underived mate already used by the fixed derived composition comparison. 
(blueprint: lem-pc-perfect-hom-cochain-counit)
-/
noncomputable def perfectHomTensorComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
      Scheme.Modules.tensorPullback (f ≫ g) :=
  (conjugateIsoEquiv
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
    (Scheme.Modules.pushforwardComp f g).symm

/-- Successive tensor pullbacks, with the exact mate used by derived composition. 
(blueprint: lem-pc-perfect-hom-cochain-counit)
-/
noncomputable def perfectHomTensorHomotopyComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    perfectHomTensorHomotopy g ⋙ perfectHomTensorHomotopy f ≅
      perfectHomTensorHomotopy (f ≫ g) :=
  let := perfectHomTensorAdditive f
  let := perfectHomTensorAdditive g
  let := perfectHomTensorAdditive (f ≫ g)
  Functor.mapHomotopyCategoryCompIso (perfectHomTensorComp f g) (.up ℤ)

/-- The fixed underived composition mate on cochain complexes. 
(blueprint: lem-pc-perfect-hom-cochain-counit)
-/
noncomputable def perfectHomTensorComplexComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    perfectHomTensorComplex g ⋙ perfectHomTensorComplex f ≅
      perfectHomTensorComplex (f ≫ g) :=
  let := perfectHomTensorAdditive f
  let := perfectHomTensorAdditive g
  let := perfectHomTensorAdditive (f ≫ g)
  Functor.mapHomologicalComplexCompIso (perfectHomTensorComp f g) (.up ℤ)

/-- Homotopy tensor pullback sends quotient maps to quotient maps of termwise pullback.
Source: the quotient construction; Stacks Project, Tag 0D5S.
(blueprint: lem-pc-perfect-hom-cochain-counit). -/
theorem perfectHomTensorHomotopy_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (m : K ⟶ L) :
    (perfectHomTensorHomotopy f).map ((HomotopyCategory.quotient _ (.up ℤ)).map m) =
      (HomotopyCategory.quotient _ (.up ℤ)).map ((perfectHomTensorComplex f).map m) := rfl

/-- The homotopy comparison is the quotient of the termwise comparison.
Source: the quotient construction; Stacks Project, Tag 0D5S.
(blueprint: lem-pc-perfect-hom-cochain-counit). -/
theorem perfectHomTensorHomotopyComp_hom_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
    (perfectHomTensorHomotopyComp f g).hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((perfectHomTensorComplexComp f g).hom.app K) := rfl

/-- The defining counit equation for the fixed derived comparison, at a homotopy model.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-perfect-hom-cochain-counit).
Proof: the fixed comparison is the left-derived lift of the composite counits.
The factorization equation of this lift gives the result after evaluating at K
and removing the identity components of functor associators. No flatness is used. -/
theorem perfectHomTensorCounit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)) :
    (perfectHomComposition f g).hom.app (DerivedCategory.Qh.obj K) ≫
        (perfectHomTensorCounit (f ≫ g)).app K =
      (derivedPullback f).map ((perfectHomTensorCounit g).app K) ≫
        (perfectHomTensorCounit f).app ((perfectHomTensorHomotopy g).obj K) ≫
        DerivedCategory.Qh.map ((perfectHomTensorHomotopyComp f g).hom.app K) := by
  let := perfectHomTensorAdditive f
  let := perfectHomTensorAdditive g
  let := perfectHomTensorAdditive (f ≫ g)
  let hL := Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)) (f ≫ g)
  have hp := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))).1 f g
  change (perfectHomComposition f g).hom = _ at hp
  rw [hp]
  rw [Functor.leftDerived_fac_app]
  simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

end AlgebraicGeometry
