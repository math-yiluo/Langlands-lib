/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # The pinned derived adjunction on single complexes
Source: Stacks Project, cohomology.tex, Tag 079W; derived.tex, Tags 08J5 and 06XS.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry

-- Keep tensor/sheafification and derived-localization data behind their functor APIs.
attribute [local irreducible] Scheme.Modules.tensorPullbackObj Scheme.Modules.tensorPullbackMap
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

private theorem single_complex_transpose
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasZeroObject D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    (adj : L ⊣ R) (N : C) (M : D) (b : L.obj N ⟶ M) (q : ℤ) :
    (adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _
      ((HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℤ) q).hom.app N ≫
        (CochainComplex.singleFunctor D q).map b) =
      (CochainComplex.singleFunctor C q).map (adj.homEquiv _ _ b) ≫
        (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℤ) q).inv.app M := by
  rw [Adjunction.homEquiv_apply]
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = q
  · subst i
    simp [Adjunction.homEquiv_apply, CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, Category.assoc]
  · apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q N i hi).eq_of_src

private theorem single_homotopy_transpose
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasZeroObject D]
    [(HomotopyCategory.quotient C (ComplexShape.up ℤ)).IsLocalization
      (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ))]
    [(HomotopyCategory.quotient D (ComplexShape.up ℤ)).IsLocalization
      (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    (adj : L ⊣ R) (N : C) (M : D) (b : L.obj N ⟶ M) (q : ℤ) :
    (adj.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv _ _
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℤ) q).hom.app N ≫
          (CochainComplex.singleFunctor D q).map b)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((CochainComplex.singleFunctor C q).map (adj.homEquiv _ _ b) ≫
          (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℤ) q).inv.app M) := by
  rw [Adjunction.homEquiv_apply]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map _ ≫
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map _ = _
  rw [← Functor.map_comp]
  exact congrArg ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map)
    (single_complex_transpose adj N M b q)

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The right-derived unit on a single complex in an arbitrary integer degree.
This extends the existing degree-zero comparison by the same termwise construction.
Source: Stacks Project, cohomology.tex, Tag 079W.
(blueprint: lem-weil-pbc-integer-single-adjunction-transpose). -/
@[irreducible] def topEdgeSingleDirectImageMap {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) :
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).obj
        ((Scheme.Modules.pushforward g).obj M) ⟶
    (schemeDerivedDirectImage g).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj M) :=
  cast (by rfl) (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom) (ComplexShape.up ℤ) q).inv.app M)) ≫
    (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      ((HomotopyCategory.singleFunctor _ q).obj M))

-- Comparing the pinned sheaf adjunction to its normalized construction needs extra heartbeats.
/-- The pinned derived adjunction on a single complex in any integer degree.
Source: Stacks Project, cohomology.tex, Tag 079W; sheaves.tex, Tag 0096.
(blueprint: lem-weil-pbc-integer-single-adjunction-transpose).

Proof: Apply the defining normalization of the selected derived adjunction to the
homotopy-category map consisting of the single pullback comparison followed by the
single of b. The termwise ordinary adjunction sends this composite to the single of
the ordinary transpose followed by the inverse single/direct-image comparison.
Pass this equality through homotopy localization and append the right-derived unit.
This is exactly the displayed formula, including the fixed pullback counit. -/
theorem topEdgeSingleAdjunctionTranspose {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    (N : S.Modules) (M : T.Modules) (b : (Scheme.Modules.tensorPullback g).obj N ⟶ M) :
    let adj := @pinnedDerivedAdjunction.{u, w} _
      (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f) _ _ g
    let a := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
    adj.homEquiv _ _ (pinnedModulePullbackComparisonAt g q N ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).map b) =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map (a.homEquiv _ _ b) ≫
        topEdgeSingleDirectImageMap g q M := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} g
  let a := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let k := (HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback g) (ComplexShape.up ℤ) q).hom.app N ≫
          (CochainComplex.singleFunctor _ q).map b)
  have hk := single_homotopy_transpose a N M b q
  let ε := @pinnedPullbackCounit.{u, w} _
    (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f) _ _ g
  let hε := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) g
  have h := Classical.choose_spec (exists_schemeDerivedAdjunction g ε hε)
    ((HomotopyCategory.singleFunctor _ q).obj N)
    ((HomotopyCategory.singleFunctor _ q).obj M) k
  have h' := h.trans (congrArg (fun z ↦ DerivedCategory.Qh.map z ≫
    (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj M)) hk)
  simp only [pinnedModulePullbackComparisonAt, derivedSingleComparisonOfCounit,
    topEdgeSingleDirectImageMap, cast_eq, k, ε,
    DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc] at h' ⊢
  exact h'

end AlgebraicGeometry
