/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystem
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Systems for canonical tower classes

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-systems).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local instance 4000] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify

/-- Towers of abelian sheaves. Source: classes (1) (blueprint: def-sp-tower-class-systems). -/
abbrev Ab (T : Scheme.{u}) := ℕᵒᵖ ⥤ DiagonalAb T

/-- The existing abelian structure on towers, shared by name to avoid rebuilding
its sheafification witnesses. Source: classes (1)--(2)
(blueprint: def-sp-tower-class-systems). -/
instance (priority := 3000) towerAbelian (T : Scheme.{u}) : Abelian (Ab T) :=
  inferInstance

/-- Ordinary localization. Source: classes (1)--(2)
(blueprint: def-sp-tower-class-systems). -/
instance abDerived (T : Scheme.{u}) : HasDerivedCategory.{u + 2} (Ab T) :=
  HasDerivedCategory.standard _

/-- Ext in the same localization. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
instance abExt (T : Scheme.{u}) : HasExt.{u + 2} (Ab T) := HasExt.standard (Ab T)

/-- Constant towers. Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
def constant (T : Scheme.{u}) : DiagonalAb T ⥤ Ab T :=
  Functor.const (ℕᵒᵖ) (C := DiagonalAb T)

/-- Exactness of the actual constant-system functor.
Source: classes (2) (blueprint: def-sp-tower-class-systems).
Proof: limits and colimits in the functor category are levelwise, so the
constant-system functor preserves them, including the additive group laws. -/
theorem constant_exact (T : Scheme.{u}) :
    (constant T).Additive ∧ PreservesFiniteLimits (constant T) ∧
      PreservesFiniteColimits (constant T) := by
  unfold constant
  exact ⟨⟨fun {_ _ _ _} ↦ rfl⟩, inferInstance, inferInstance⟩

/-- Additivity of constant systems. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
instance constantAdditive (T : Scheme.{u}) : (constant T).Additive :=
  (constant_exact T).1

/-- Left exactness of constant systems. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
instance constantLimits (T : Scheme.{u}) : PreservesFiniteLimits (constant T) :=
  (constant_exact T).2.1

/-- Right exactness of constant systems. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
instance constantColimits (T : Scheme.{u}) : PreservesFiniteColimits (constant T) :=
  (constant_exact T).2.2

/-- Integral coefficients. Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
abbrev integers (T : Scheme.{u}) :=
  (constant T).obj ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The actual roots tower. Source: classes (1) (blueprint: def-sp-tower-class-systems). -/
abbrev roots (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)

/-- Power-transition units. Source: classes (1) (blueprint: def-sp-tower-class-systems). -/
def powerUnits (l : ℕ) (T : Scheme.{u}) : Ab T :=
  Functor.ofOpSequence (X := fun _ : ℕ ↦ Scheme.proEtaleUnitsSheaf T)
    (fun _ ↦ Scheme.proEtaleUnitsPower T l)

/-- Identity-transition units. Source: classes (1)
(blueprint: def-sp-tower-class-systems). -/
abbrev units (T : Scheme.{u}) := (constant T).obj (Scheme.proEtaleUnitsSheaf T)

/-- The exact sequence uses the actual inclusions and power maps at every positive level.
Source: classes (1) (blueprint: def-sp-tower-class-systems). -/
structure Kummer (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) where
  inclusion : roots l T ⟶ powerUnits l T
  inclusion_eq : ∀ n : ℕ,
    inclusion.app (op n) = Scheme.proEtaleRootsOfUnityInclusion T (l ^ (n + 1))
  power : powerUnits l T ⟶ units T
  power_eq : ∀ n : ℕ, power.app (op n) = Scheme.proEtaleUnitsPower T (l ^ (n + 1))
  zero : inclusion ≫ power = 0
  exact : (ShortComplex.mk inclusion power zero).ShortExact

/-- Ringed sequence-site systems, with the dependency's exact site universes.
Source: coefficient towers and classes (2) (blueprint: def-sp-tower-class-systems). -/
abbrev Systems (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :=
  SemilinearSections.Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)

/-- Share the published abelian witness of the ringed sequence-site category.
Source: classes (2), the recorded system model (blueprint: def-sp-tower-class-systems). -/
instance (priority := 5000) systemsAbelian (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    Abelian (Systems T B) :=
  SemilinearSections.moduleAbelian.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op))

/-- The ordinary derived category of these systems.
Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
abbrev D (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :=
  DerivedCategory (Systems T B)

/-- The actual coefficient module, not a free source-object parameter.
Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
def coefficient (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) : Systems T B :=
  SheafOfModules.unit (SemilinearSections.ring.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)))

/-- Coefficients in degree zero. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
abbrev unit (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :=
  (DerivedCategory.singleFunctor (Systems T B) 0).obj (coefficient T B)

/-- The canonical forgetful functor is specified on every section, restriction and map.
These equalities identify a functor, rather than assuming a free map between categories.
Source: classes (2), modules in the inverse-system topos
(blueprint: def-sp-tower-class-systems). -/
structure Forget (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) where
  F : Systems T B ⥤ Ab T
  sections : ∀ (M : Systems T B) (n : ℕ) (U : T.ProEtᵒᵖ),
    ((F.obj M).obj (op n)).obj.obj U =
      AddCommGrpCat.of (M.val.obj (op (n, U.unop)))
  restrictions : ∀ (M : Systems T B) (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V),
    HEq ((((F.obj M).obj (op n)).obj.map f).hom)
      ((M.val.map (Prod.mkHom (𝟙 n) f.unop).op).hom.toAddMonoidHom)
  transitions : ∀ (M : Systems T B) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ),
    HEq ((((F.obj M).map (homOfLE h).op).hom.app U).hom)
      ((M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom.toAddMonoidHom)
  morphisms : ∀ {M N : Systems T B} (f : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq ((((F.map f).app (op n)).hom.app U).hom)
      ((f.val.app (op (n, U.unop))).hom.toAddMonoidHom)
  [additive : F.Additive]
  [limits : PreservesFiniteLimits F]
  [colimits : PreservesFiniteColimits F]

attribute [instance] Forget.additive Forget.limits Forget.colimits

private theorem cast_int_natural {A A' : AddCommGrpCat.{u + 1}}
    {R S : CommRingCat.{u + 1}}
    (e : A = AddCommGrpCat.of R) (e' : A' = AddCommGrpCat.of S)
    (f : A ⟶ A') (g : R ⟶ S) (h : HEq f.hom g.hom.toAddMonoidHom) (k : ℤ) :
    f ((eqToHom e.symm) (k : R)) = (eqToHom e'.symm) (k : S) := by
  subst A
  subst A'
  have hh := eq_of_heq h
  change f.hom (k : R) = (k : S)
  rw [hh]
  exact map_intCast g.hom k

private theorem coefficientGroupEq (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) (U : T.ProEtᵒᵖ) :
    ((F.F.obj (coefficient T B)).obj (op n)).obj.obj U =
      AddCommGrpCat.of ((B.obj (op n)).obj.obj U) :=
  F.sections (coefficient T B) n U

private def integerSectionMap (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) (U : T.ProEtᵒᵖ) :
    AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
      ((F.F.obj (coefficient T B)).obj (op n)).obj.obj U :=
  AddCommGrpCat.ofHom
    (((eqToHom (coefficientGroupEq T B F n U).symm).hom).comp
      ((Int.castAddHom ((B.obj (op n)).obj.obj U)).comp
        AddEquiv.ulift.toAddMonoidHom))

private abbrev coefficientRingPresheaf (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :=
  SemilinearSections.ringPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)

private theorem integerSectionMap_restrictions (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V) :
    integerSectionMap T B F n U ≫
      ((F.F.obj (coefficient T B)).obj (op n)).obj.map f =
        integerSectionMap T B F n V := by
  ext k
  apply cast_int_natural (coefficientGroupEq T B F n U)
    (coefficientGroupEq T B F n V) _
    ((coefficientRingPresheaf T B).map (Prod.mkHom (𝟙 n) f.unop).op)
  exact F.restrictions (coefficient T B) n f

private theorem int_cast_transport {A : AddCommGrpCat.{u + 1}}
    {R : CommRingCat.{u + 1}} (e : A = AddCommGrpCat.of R) (k : ℤ) :
    HEq ((eqToHom e.symm) (k : R)) (k : R) := by
  subst A
  rfl

private theorem integerSectionMap_spec (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) (U : T.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ) :
    HEq (integerSectionMap T B F n U k) (k.down : (B.obj (op n)).obj.obj U) :=
  int_cast_transport (coefficientGroupEq T B F n U) k.down

private def integerPresheafMap (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) :
    (Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      ((F.F.obj (coefficient T B)).obj (op n)).obj where
  app := integerSectionMap T B F n
  naturality U V f := by
    change 𝟙 _ ≫ integerSectionMap T B F n V =
      integerSectionMap T B F n U ≫ _
    rw [Category.id_comp]
    exact (integerSectionMap_restrictions T B F n f).symm

private def integerLevelMap (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) :
    (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
        (F.F.obj (coefficient T B)).obj (op n) where
  hom := sheafifyLift (Scheme.ProEt.topology T) (integerPresheafMap T B F n)
    ((F.F.obj (coefficient T B)).obj (op n)).property

private theorem integerLevelMap_spec (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) (U : T.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ) :
    HEq ((integerLevelMap T B F n).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k))
      (k.down : (B.obj (op n)).obj.obj U) := by
  have h := congrArg (fun a ↦ a.app U k)
    (toSheafify_sheafifyLift (Scheme.ProEt.topology T) (integerPresheafMap T B F n)
      ((F.F.obj (coefficient T B)).obj (op n)).property)
  exact h.heq.trans (integerSectionMap_spec T B F n U k)

private theorem integerSectionMap_transitions (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) (U : T.ProEtᵒᵖ) :
    integerSectionMap T B F (n + 1) U ≫
      ((F.F.obj (coefficient T B)).map (homOfLE (Nat.le_succ n)).op).hom.app U =
        integerSectionMap T B F n U := by
  ext k
  apply cast_int_natural (coefficientGroupEq T B F (n + 1) U)
    (coefficientGroupEq T B F n U) _
    ((coefficientRingPresheaf T B).map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op)
  exact F.transitions (coefficient T B) (Nat.le_succ n) U

private theorem integerLevelMap_transitions (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) :
    integerLevelMap T B F (n + 1) ≫
      (F.F.obj (coefficient T B)).map (homOfLE (Nat.le_succ n)).op =
        integerLevelMap T B F n := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology T) _ _
    ((F.F.obj (coefficient T B)).obj (op n)).property
  change toSheafify _ _ ≫ (sheafifyLift _ (integerPresheafMap T B F (n + 1)) _ ≫
    ((F.F.obj (coefficient T B)).map (homOfLE (Nat.le_succ n)).op).hom) =
      toSheafify _ _ ≫ sheafifyLift _ (integerPresheafMap T B F n) _
  rw [← Category.assoc, toSheafify_sheafifyLift, toSheafify_sheafifyLift]
  ext U k
  exact congrArg (fun a ↦ a k) (integerSectionMap_transitions T B F n U)

/-- The quotient of the constant integer tower is fixed on every constant section.
Source: classes (2), coefficient unit (blueprint: def-sp-tower-class-systems).
Proof: at each level the integer acts on the coefficient unit by its integer
multiple of one. This commutes with restrictions and quotient transitions;
the constant-sheaf universal property gives existence and uniqueness. -/
theorem integerGenerator_existsUnique (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) :
    ∃! f : integers T ⟶ F.F.obj (coefficient T B),
      ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ),
        HEq (((f.app (op n)).hom.app U)
          ((toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k))
          (k.down : (B.obj (op n)).obj.obj U) := by
  let f : integers T ⟶ F.F.obj (coefficient T B) :=
    NatTrans.ofOpSequence (integerLevelMap T B F) (fun n ↦ by
      change 𝟙 _ ≫ integerLevelMap T B F n = integerLevelMap T B F (n + 1) ≫ _
      rw [Category.id_comp]
      exact (integerLevelMap_transitions T B F n).symm)
  refine ⟨f, integerLevelMap_spec T B F, ?_⟩
  intro g hg
  apply NatTrans.ext
  funext n
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology T) _ _
    ((F.F.obj (coefficient T B)).obj n).property
  ext U k
  exact eq_of_heq ((hg n.unop U k).trans (integerLevelMap_spec T B F n.unop U k).symm)

/-- The canonical integer-to-coefficient quotient, fixed by constant generators.
Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
def integerGenerator (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) : integers T ⟶ F.F.obj (coefficient T B) :=
  (integerGenerator_existsUnique T B F).exists.choose

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
