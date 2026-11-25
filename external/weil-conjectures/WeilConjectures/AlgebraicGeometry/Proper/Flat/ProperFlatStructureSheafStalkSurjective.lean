/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Proper.Flat.ProperFlatSingleDerivedDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectLocalDegreeZeroUnit
import WeilConjectures.AlgebraicGeometry.Flat.FlatDerivedStructureUnit
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Surjectivity of the structure-sheaf map for proper flat morphisms

## References

* Stacks Project, Tag 0E62 (localized at a point); Tag 0BCD for the minimal finite free model
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem surjective_of_comp_isIso {A B C : Ab.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsIso b] (h : Function.Surjective (a ≫ b)) : Function.Surjective a := by
  intro y
  obtain ⟨x, hx⟩ := h (b y)
  refine ⟨x, (ConcreteCategory.bijective_of_isIso b).1 ?_⟩
  simpa only [ConcreteCategory.comp_apply] using hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For a proper flat morphism `f` of finite presentation such that `κ(s) → Γ(X_s, 𝒪)` is an
isomorphism, the stalk at `s` of the canonical map `𝒪_S → f_* 𝒪_X` is surjective. -/
theorem surjective_structureSheafMap_stalk_of_proper_flat_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (s : S)
    (hs : IsIso (f.fiberToSpecResidueField s).appTop) :
    Function.Surjective
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)).stalkLinearMap s) := by
  classical
  let : ∀ Y : Scheme.{u},
      HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    fun Y ↦ HasDerivedCategory.standard _
  let : ∀ U : S.Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  let : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive := by
    intro Y Z k
    let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
    let : (Scheme.Modules.tensorPullback k).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  let OX := SheafOfModules.unit X.ringCatSheaf
  let E := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj OX)
  have : SheafOfModules.IsInvertible.{u, u, u} OX :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} OX := inferInstance
  have : OX.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation OX
  have hflat : Scheme.Modules.IsFlatOver OX f :=
    Scheme.Modules.isFlatOver_of_isInvertible f OX
  have hperfect : Scheme.IsPerfect S E :=
    properFlat_single_derivedDirectImage_perfect f OX hflat
  obtain ⟨a, e₀, e₁, hcomp, hnegative, hfibre⟩ :=
    exists_flat_derived_structure_unit f
  have hsurj := surjective_stalk_homology_of_perfect_local_unit S E hperfect a s
    (hnegative s) (hfibre s hs)
  let F := SheafOfModules.forget S.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} s
  have hsurj' : Function.Surjective (F.map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a)) := hsurj
  let q : SheafOfModules.unit S.ringCatSheaf ⟶
      (Scheme.Modules.pushforward f).obj OX :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hcomp' : F.map ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a) ≫ F.map e₁.hom =
      F.map e₀.hom ≫ F.map q := by
    simpa only [Functor.map_comp] using
      congrArg (fun t ↦ F.map t) hcomp
  have hord : Function.Surjective
      (F.map q) := by
    intro y
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso (F.map e₁.hom)).2 y
    obtain ⟨x, hx⟩ := hsurj' z
    refine ⟨F.map e₀.hom x, ?_⟩
    have h := congrArg (fun q ↦ q x) hcomp'
    simpa only [ConcreteCategory.comp_apply, hx, hz] using h.symm
  obtain ⟨hb, hunit⟩ := Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f
  let b := (Scheme.Modules.pushforward f).map
    (Scheme.Modules.tensorPullbackObjUnitToUnit f)
  have : IsIso (Scheme.Modules.tensorPullbackObjUnitToUnit f) := hb
  have : IsIso b := Functor.map_isIso _ _
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
    (SheafOfModules.unit S.ringCatSheaf)
  have hunit' : F.map η ≫ F.map b = F.map q := by
    simpa only [Functor.map_comp] using congrArg (fun t ↦ F.map t) hunit
  change Function.Surjective (F.map η)
  apply surjective_of_comp_isIso (F.map η) (F.map b)
  rw [hunit']
  exact hord

end AlgebraicGeometry
