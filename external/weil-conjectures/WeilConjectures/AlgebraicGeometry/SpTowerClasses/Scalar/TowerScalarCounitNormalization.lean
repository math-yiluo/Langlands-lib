/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarSingleCounit
import Mathlib.Algebra.Homology.Monoidal

/-! # Normalized scalar counit on the coefficient module
Source: blueprint classes proof (2), scalar coefficient normalization.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c d
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem coefficientKFlat (T : Scheme.{u})
    (R : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (fun n ↦ R.obj (op n))
        (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op))
      ((HomologicalComplex.single (Systems T R) (.up ℤ) 0).obj (coefficient T R)) := by
  intro F hF i
  exact HomologicalComplex.ExactAt.of_iso (e := (HomologicalComplex.rightUnitor F).symm)
    (hF i)

private theorem singleAdjunct
    {C : Type a} [Category.{b} C] [Abelian C]
    {D : Type c} [Category.{d} D] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    ((adj.mapHomologicalComplex (.up ℤ)).homEquiv
      ((HomologicalComplex.single C (.up ℤ) 0).obj X)
      ((HomologicalComplex.single D (.up ℤ) 0).obj Y))
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X ≫
          (HomologicalComplex.single D (.up ℤ) 0).map f) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app Y =
      (HomologicalComplex.single C (.up ℤ) 0).map ((adj.homEquiv X Y) f) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
    Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc]
  simp only [← G.map_comp_assoc, Iso.inv_hom_id_assoc]
  rw [G.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [← adj.unit.naturality_assoc]
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The normalized ordinary scalar counit on the coefficient module.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
scalar extension; Stacks 06YY and 07A6.
(blueprint: lem-sp-tower-scalar-counit-normalization).

Proof: the coefficient module in degree zero is K-flat by the cochain tensor right
unitor. Apply the representative transpose formula of `ScalarData` to the induced
chain map from the ordinary coefficient arrow `e`. The adjunction on single
complexes has the ordinary adjunct as its degree-zero component. The exact
restriction single comparison identifies this derived transpose with the single of
`scalarGenerator`. The third Chern normalization gives the same transpose for
`scalarUnit`. Cancel the single comparison and use injectivity of the derived Hom
equivalence. This proves the displayed ordinary counit equation. -/
theorem scalarCounitNormalization {T : Scheme.{u}} (c : Chern l E T)
    (nc : c.Normalized l E)
    (e : c.scalar.model.E.obj (coefficient T (Rrings l T)) ⟶
      coefficient T (Arings l E T))
    (he : (c.scalar.ordinaryAdjunction.homEquiv _ _) e = scalarGenerator l E T) :
    (scalarSingleCounit c).app (coefficient T (Rrings l T)) ≫
        (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).map e =
      c.scalarUnit.hom := by
  let s := c.scalar
  let G := SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T)
  let P := (HomologicalComplex.single (Systems T (Rrings l T)) (.up ℤ) 0).obj
    (coefficient T (Rrings l T))
  let Q := (HomologicalComplex.single (Systems T (Arings l E T)) (.up ℤ) 0).obj
    (coefficient T (Arings l E T))
  let f : (s.model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q :=
    (HomologicalComplex.singleMapHomologicalComplex s.model.E (.up ℤ) 0).hom.app
      (coefficient T (Rrings l T)) ≫
        (HomologicalComplex.single _ (.up ℤ) 0).map e
  have ht := s.transpose_model P Q (coefficientKFlat T (Rrings l T)) f
  have hg : (G.mapDerivedCategorySingleFunctor 0).hom.app
      (coefficient T (Arings l E T)) =
      G.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app
          (coefficient T (Arings l E T))) := by
    erw [← G.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
    erw [Iso.hom_inv_id_app_assoc]
  have hf : ((s.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P Q) f ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app
        (coefficient T (Arings l E T)) =
      (HomologicalComplex.single _ (.up ℤ) 0).map
        ((s.ordinaryAdjunction.homEquiv _ _) e) := by
    exact singleAdjunct s.ordinaryAdjunction e
  have hrep : (scalarSingleCounit c).app (coefficient T (Rrings l T)) ≫
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).map e =
      s.model.ε.app P ≫ DerivedCategory.Q.map f := by
    simp only [scalarSingleCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom,
      Iso.refl_inv, NatTrans.id_app, Functor.map_comp, f]
    erw [s.T.map_id]
    simp only [Category.assoc]
    erw [Category.id_comp, Category.id_comp]
    rfl
  apply (s.adjunction.homEquiv _ _).injective
  apply (cancel_mono ((G.mapDerivedCategorySingleFunctor 0).hom.app
    (coefficient T (Arings l E T)))).1
  have hn := nc.2.2
  change (s.adjunction.homEquiv _ _) c.scalarUnit.hom ≫
    (G.mapDerivedCategorySingleFunctor 0).hom.app (coefficient T (Arings l E T)) =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map
        (scalarGenerator l E T) at hn
  rw [hn, hrep, hg, ← Category.assoc]
  erw [ht]
  rw [← Functor.map_comp, hf, he]
  rfl
end AlgebraicGeometry.ProEtale.SpTowerClasses
