/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import Mathlib.Algebra.Homology.Monoidal

/-! # The scalar comparison on the coefficient unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a b c d
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open WeilConjectures
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

/-- Scalar extension carries the coefficient unit to the coefficient unit, with
its comparison fixed by the ordinary quotient ring map.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
scalar extension; Stacks 06YY and 07A6.
(blueprint: lem-sfb-tower-chern-scalar-unit).

Proof: the unit in degree zero is K-flat, since tensoring an acyclic complex
with it is isomorphic to that complex by the tensor unitor. The universal scalar
counit therefore computes its derived extension. Ordinary scalar extension of
the unit is the target ring by multiplication, with inverse a mapping to a
tensor one. Compose this multiplication isomorphism with the counit and the
single-complex comparisons. The representative transpose equation identifies
its adjunct with the ordinary unit followed by multiplication. On every section
this is x mapping to phi(x). The defining uniqueness of scalarGenerator gives
the required normalization. No flatness of the ring map is used. -/
theorem exists_normalizedScalarUnit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u})
    (s : SemilinearSections.ScalarData.{u + 1, u, u + 1}
      (coefficientSystemMap l E T)) :
    ∃ e : s.T.obj (unit T (Rrings l T)) ≅ unit T (Arings l E T),
      unitNormalization s.T (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E T)) s.adjunction e (scalarGenerator l E T) := by
  let φ := coefficientSystemMap l E T
  obtain ⟨d⟩ := SheafOfModules.scalarExtension_constraint_coherence
    (SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (fun n ↦ (Rrings l T).obj (op n))
      (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op))
    (SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)) φ
  let e₀ : s.model.E.obj (coefficient T (Rrings l T)) ≅
      coefficient T (Arings l E T) :=
    eqToIso (s.model.obj_eq _) ≪≫ d.unitIso
  let P := (HomologicalComplex.single (Systems T (Rrings l T)) (.up ℤ) 0).obj
    (coefficient T (Rrings l T))
  have hP := coefficientKFlat T (Rrings l T)
  have := s.model.computes P hP
  let e : s.T.obj (unit T (Rrings l T)) ≅ unit T (Arings l E T) :=
    s.T.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
      asIso (s.model.ε.app P) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex s.model.E (.up ℤ) 0).app _) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (Systems T (Arings l E T)) 0).app
        (s.model.E.obj (coefficient T (Rrings l T)))).symm ≪≫
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).mapIso e₀
  have he₀ : (s.ordinaryAdjunction.homEquiv _ _) e₀.hom = scalarGenerator l E T := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hq := (scalarGenerator_existsUnique l E T).exists.choose_spec U x
    change e₀.hom.val.app U
      ((s.ordinaryAdjunction.unit.app (coefficient T (Rrings l T))).val.app U x) = _
    change d.unitIso.hom.val.app U
      ((eqToHom (s.model.obj_eq _)).val.app U
        ((s.ordinaryAdjunction.unit.app (coefficient T (Rrings l T))).val.app U x)) = _
    erw [s.unit_section]
    calc
      _ = φ.hom.app U x := by
        have h := d.unit_hom U 1 x
        change d.unitIso.hom.val.app U
          (SemilinearSections.extensionUnit (coefficientSystemMap l E T)
            (coefficient T (Rrings l T)) U x) = 1 * φ.hom.app U x at h
        have h1 := one_mul ((φ.hom.app U).hom x)
        exact h.trans h1
      _ = _ := (eq_of_heq hq).symm
  refine ⟨e, ?_⟩
  let G := SemilinearSections.res.{u + 1, u, u + 1} φ
  let Q := (HomologicalComplex.single (Systems T (Arings l E T)) (.up ℤ) 0).obj
    (coefficient T (Arings l E T))
  let f : (s.model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q :=
    (HomologicalComplex.singleMapHomologicalComplex s.model.E (.up ℤ) 0).hom.app
      (coefficient T (Rrings l T)) ≫
        (HomologicalComplex.single _ (.up ℤ) 0).map e₀.hom
  have ht := s.transpose_model P Q hP f
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
        ((s.ordinaryAdjunction.homEquiv _ _) e₀.hom) := by
    exact singleAdjunct s.ordinaryAdjunction e₀.hom
  have he : e.hom = s.model.ε.app P ≫ DerivedCategory.Q.map f := by
    simp only [e, f, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
      DerivedCategory.singleFunctorIsoCompQ, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [s.T.map_id]
    simp only [Category.id_comp, Functor.map_comp]
    rfl
  unfold unitNormalization
  change (s.adjunction.homEquiv (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj Q)) e.hom ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (coefficient T (Arings l E T)) =
        (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map
          (scalarGenerator l E T)
  rw [he, hg, ← Category.assoc]
  erw [ht]
  rw [← Functor.map_comp, hf, he₀]
  rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses
