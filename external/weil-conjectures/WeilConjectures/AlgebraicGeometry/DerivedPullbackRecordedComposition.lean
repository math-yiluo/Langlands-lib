/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionIsIso

/-! # Composition using the original derived-pullback presentation

The universal functor and its counit are retained as one presentation. In particular,
we do not select a fresh counit for an already fixed functor from the composition
existence theorem. Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-pc-recorded-pullback-composition).
-/

@[expose] public section

universe u w
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The tensor functor and universal counit in the original derived-pullback presentation.
The additive instance is included so all homotopy functors use the same presentation.
Source: Stacks Project, Tag 06YJ (blueprint: lem-pc-recorded-pullback-composition). -/
structure RecordedPullbackData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  E : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
    SheafOfModules.{u} (moduleRings X.toRingedSpace)
  obj_eq : ∀ M, E.obj M = Scheme.Modules.tensorPullbackObj f M
  map_eq : ∀ {M N} (a : M ⟶ N), E.map a =
    eqToHom (obj_eq M) ≫ Scheme.Modules.tensorPullbackMap f a ≫ eqToHom (obj_eq N).symm
  additive : E.Additive
  ε : letI := additive
    DerivedCategory.Qh ⋙ derivedPullback f ⟶
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  universal : letI := additive
    (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
  kFlat : letI := additive
    ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))

/-- Project the complete original witness used to define `derivedPullback`.
The choices project successive fields of that witness. We retain this primary counit
once, rather than choosing a fresh counit for the fixed functor from a later existence
statement. Its universal functor/counit pair is determined up to the compatible
isomorphism used for derived computations. Irreducibility avoids unfolding the nested
witness selections when using the field equations below.
Source: Stacks Project, Tag 06YJ (blueprint: lem-pc-recorded-pullback-composition). -/
@[irreducible] noncomputable def recordedPullbackData {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RecordedPullbackData f := by
  classical
  choose I hI hImap hIa hprops using (derivedPullback_spec f)
  choose E hE hEmap hEa ε hε using hprops.2.2.2
  exact ⟨E, hE, hEmap, hEa, ε, hε.1, hε.2.2⟩

/-- Equality of the recorded tensor functor with the fixed tensor formula.
Source: Stacks Project, Tag 06YJ (blueprint: lem-pc-recorded-pullback-composition). -/
theorem recordedPullbackData_E {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (recordedPullbackData f).E = Scheme.Modules.tensorPullback f :=
  CategoryTheory.Functor.ext (recordedPullbackData f).obj_eq
    (fun _ _ a ↦ (recordedPullbackData f).map_eq a)

/-- Additivity of the tensor pullback in the original presentation.
Source: Stacks Project, Tag 06YJ (blueprint: lem-pc-recorded-pullback-composition). -/
theorem recordedPullbackData_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (recordedPullbackData f).E.Additive :=
  (recordedPullbackData f).additive

/-- Transport a counit along equality of its underived tensor functors.
This is equality transport, with no selection of natural-transformation data.
Source: Stacks Project, Tag 06YJ (blueprint: lem-pc-recorded-pullback-composition). -/
noncomputable def recordedTransportCounit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E E' : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [E.Additive] [E'.Additive]
    (h : E = E')
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Qh ⋙ derivedPullback f ⟶
      E'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh := by
  cases h
  exact ε

private theorem transportCounit_universal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E E' : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [E.Additive] [E'.Additive]
    (h : E = E')
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))) :
    (derivedPullback f).IsLeftDerivedFunctor (recordedTransportCounit f E E' h ε)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) := by
  cases h
  exact hε

private theorem transportCounit_kFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E E' : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [E.Additive] [E'.Additive]
    (h : E = E')
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hε : IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :
    IsIso ((recordedTransportCounit f E E' h ε).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  cases h
  exact hε

/-- The original counit, transported along equality of the tensor-formula functors.
Source: Stacks Project, Tag 06YJ (blueprint: lem-pc-recorded-pullback-composition). -/
@[irreducible] noncomputable def recordedDerivedPullbackCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI : (Scheme.Modules.tensorPullback f).Additive := by
      rw [← recordedPullbackData_E f]
      exact recordedPullbackData_additive f
    DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) := by
  let : (Scheme.Modules.tensorPullback f).Additive := by
    simpa only [recordedPullbackData_E] using recordedPullbackData_additive f
  letI := (recordedPullbackData f).additive
  exact recordedTransportCounit f (recordedPullbackData f).E (Scheme.Modules.tensorPullback f)
    (recordedPullbackData_E f) (recordedPullbackData f).ε

/-- The retained counit has the original universal property.
Source: Stacks Project, Tag 06YJ (blueprint: lem-pc-recorded-pullback-composition). -/
theorem recordedDerivedPullbackCounit_universal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback f).IsLeftDerivedFunctor (recordedDerivedPullbackCounit f)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) := by
  let : (Scheme.Modules.tensorPullback f).Additive := by
    simpa only [recordedPullbackData_E] using recordedPullbackData_additive f
  let : (recordedPullbackData f).E.Additive := (recordedPullbackData f).additive
  unfold recordedDerivedPullbackCounit
  exact transportCounit_universal f (recordedPullbackData f).E
    (Scheme.Modules.tensorPullback f) (recordedPullbackData_E f)
    (recordedPullbackData f).ε (recordedPullbackData f).universal

/-- The retained counit computes pullback on K-flat complexes.
Source: Stacks Project, Tag 06YJ (blueprint: lem-pc-recorded-pullback-composition). -/
theorem recordedDerivedPullbackCounit_kFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Y.sheaf) P) :
    IsIso ((recordedDerivedPullbackCounit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  let : (Scheme.Modules.tensorPullback f).Additive := by
    simpa only [recordedPullbackData_E] using recordedPullbackData_additive f
  let : (recordedPullbackData f).E.Additive := (recordedPullbackData f).additive
  unfold recordedDerivedPullbackCounit
  exact transportCounit_kFlat f (recordedPullbackData f).E
    (Scheme.Modules.tensorPullback f) (recordedPullbackData_E f)
    (recordedPullbackData f).ε P ((recordedPullbackData f).kFlat P hP)

attribute [local instance] recordedDerivedPullbackCounit_universal

/-- The explicit composite of the original counits and the canonical tensor associator.
Source: Stacks Project, Tag 0D5S (blueprint: lem-pc-recorded-pullback-composition). -/
noncomputable def recordedDerivedPullbackCompositionLift {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPullback g ⋙ derivedPullback f ⟶ derivedPullback (f ≫ g) := by
  letI : ∀ {A B : Scheme.{u}} (k : A ⟶ B), (Scheme.Modules.tensorPullback k).Additive :=
    fun k ↦ by
      rw [← recordedPullbackData_E k]
      exact recordedPullbackData_additive k
  exact (derivedPullback (f ≫ g)).leftDerivedLift (recordedDerivedPullbackCounit (f ≫ g))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
    (derivedPullback g ⋙ derivedPullback f)
    ((Functor.associator DerivedCategory.Qh (derivedPullback g) (derivedPullback f)).inv ≫
      Functor.whiskerRight (recordedDerivedPullbackCounit g) (derivedPullback f) ≫
      (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
      Functor.whiskerLeft _ (recordedDerivedPullbackCounit f) ≫
      (Functor.associator _ _
        (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))).inv ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso
          ((conjugateIsoEquiv
            (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
            ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
              (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
            (Scheme.Modules.pushforwardComp f g).symm) (ComplexShape.up ℤ)).hom
        (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))))

/-- The explicit lift is invertible by its K-flat computation.
Source: Stacks Project, Tag 0D5S (blueprint: lem-pc-recorded-pullback-composition). -/
theorem recordedDerivedPullbackCompositionLift_isIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) : IsIso (recordedDerivedPullbackCompositionLift f g) := by
  exact isIso_derivedPullbackCompositionLift
    (fun f ↦ by
      rw [← recordedPullbackData_E f]
      exact recordedPullbackData_additive f) (fun f ↦ recordedDerivedPullbackCounit f)
    (fun f ↦ recordedDerivedPullbackCounit_universal f)
    (fun f P hP ↦ recordedDerivedPullbackCounit_kFlat f P hP) f g

attribute [local instance] recordedDerivedPullbackCompositionLift_isIso

/-- Composition of derived pullbacks, constructed from the retained original counits.
Source: Stacks Project, Tag 0D5S (blueprint: lem-pc-recorded-pullback-composition). -/
noncomputable def recordedDerivedPullbackComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
  asIso (recordedDerivedPullbackCompositionLift f g)

end AlgebraicGeometry
