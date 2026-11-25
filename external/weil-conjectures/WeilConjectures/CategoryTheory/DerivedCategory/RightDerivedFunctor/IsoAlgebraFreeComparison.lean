/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFreeComparison
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction

/-!
# Free algebras and right derived transports

Let `F`, `G` be additive autoequivalences of abelian categories `C`, `D` with exact coproducts
indexed by `ℤ`, `L : C ⥤ D` an additive functor and `e : L ⋙ G ≅ F ⋙ L`. The total right derived
functor `R(mapOfNatIso e)` of the transport of algebras is computed on underlying objects by `RL`
(`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso`). This file
shows that it commutes with the derived free algebra functors `D(Free)`, in the sense that the free
comparison `D(Free)(RL M) ⟶ R(mapOfNatIso e)(D(Free) M)` is an isomorphism, for `M = Q I` with `I`
K-injective, as soon as `L` preserves the coproducts `∐ₙ Fⁿ Iᵏ` and `RL` is computed by `L` on the
complex `∐ₙ Fⁿ I`
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_freeComparison_rightDerivedFunctor`).

Indeed
`D(Free)(RL (Q I)) ≅ Q(Free (L I)) ≅ Q(mapOfNatIso e (Free I)) ≅ R(mapOfNatIso e)(Q(Free I))`:
the first isomorphism since `I` is K-injective, the second is the free comparison of algebras
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_freeComparison_mapOfNatIso`), and the third since
the unit of `R(mapOfNatIso e)` at `Free I` is an isomorphism after forgetting.
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Functor

section RightDerivedFunctorUnitQ

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B] [HasDerivedCategory A]
  [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A] (P : A ⥤ B) [P.Additive]

private lemma rightDerivedFunctorUnitQ_eq_rightDerivedFunctorUnit_app (K : CochainComplex A ℤ) :
    P.rightDerivedFunctorUnitQ K =
      P.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) := by
  simp only [rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv]
  erw [Category.id_comp, Functor.map_id, Category.comp_id]

instance (K : CochainComplex A ℤ) [K.IsKInjective] : IsIso (P.rightDerivedFunctorUnitQ K) := by
  rw [rightDerivedFunctorUnitQ_eq_rightDerivedFunctorUnit_app]
  infer_instance

end RightDerivedFunctorUnitQ

section MapDerivedCategoryFactorsh

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B] [HasDerivedCategory A]
  [HasDerivedCategory B] (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P]

/-- On the image of a complex `K` in the homotopy category, the inverse of the comparison
`P.mapDerivedCategoryFactorsh` is that of `P.mapDerivedCategoryFactors` at `K`. -/
private lemma mapDerivedCategoryFactorsh_inv_app_quotient_obj (K : CochainComplex A ℤ) :
    P.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      P.mapDerivedCategoryFactors.inv.app K := by
  refine Iso.inv_ext (f := P.mapDerivedCategoryFactorsh.app
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ?_
  rw [Iso.app_hom, mapDerivedCategoryFactorsh_hom_app]
  simp only [comp_obj, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, mapHomotopyCategoryFactors, map_id, Category.comp_id,
    Category.assoc]
  erw [Functor.map_id, Category.id_comp, Category.id_comp, Iso.hom_inv_id_app]
  rfl

end MapDerivedCategoryFactorsh

end CategoryTheory.Functor

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) D] [HasExactColimitsOfShape (Discrete ℤ) D]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]
  [Abelian.HasKInjectiveResolutions C]

attribute [local instance] Functor.preservesFiniteLimits_of_preservesHomology
  Functor.preservesFiniteColimits_of_preservesHomology

omit [HasColimitsOfShape (Discrete ℤ) D] [HasExactColimitsOfShape (Discrete ℤ) D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)] in
/-- The isomorphism `R(mapOfNatIso e) ⋙ For ≅ For ⋙ RL` is characterized by the units: the
unit of `R(mapOfNatIso e) ⋙ D(For)` followed by it is the unit of `D(For) ⋙ RL`. -/
lemma rightDerivedFunctorMapOfNatIsoCompForgetIso_hom_fac
    (X : HomotopyCategory (IsoAlgebra F) (ComplexShape.up ℤ)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit (mapOfNatIso e) (forget G)).app X ≫
        (rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (mapOfNatIsoCompForgetIso e).hom
          (ComplexShape.up ℤ)).app X) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit (forget F) L).app X := by
  simp only [rightDerivedFunctorMapOfNatIsoCompForgetIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso, Functor.rightDerivedNatIso_inv,
    Functor.rightDerivedNatTrans_app_assoc, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans, Functor.rightDerivedFunctorCompIso,
    Functor.rightDerivedNatIso_hom, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  congr 1
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, ← Functor.map_comp]
  rw [← Functor.whiskerLeft_app DerivedCategory.Qh
    (forget F).rightDerivedFunctorIsoMapDerivedCategory.hom X, ← NatTrans.comp_app,
    (forget F).rightDerivedFunctorIsoMapDerivedCategory_hom_fac]

omit [HasColimitsOfShape (Discrete ℤ) D] [HasExactColimitsOfShape (Discrete ℤ) D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)] in
/-- On a complex of algebras `K`, the isomorphism `R(mapOfNatIso e) ⋙ For ≅ For ⋙ RL` turns the
unit of `R(mapOfNatIso e)` at `K`, after forgetting, into the unit of `RL` at the underlying
complex of `K`. -/
@[reassoc]
lemma mapDerivedCategoryFactors_inv_app_comp_rightDerivedFunctorMapOfNatIsoCompForgetIso_hom
    (K : CochainComplex (IsoAlgebra F) ℤ) :
    (forget G).mapDerivedCategoryFactors.inv.app
          (((mapOfNatIso e).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (forget G).mapDerivedCategory.map ((mapOfNatIso e).rightDerivedFunctorUnitQ K) ≫
        (rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app (DerivedCategory.Q.obj K) =
      L.rightDerivedFunctorUnitQ (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        L.rightDerivedFunctor.map ((forget F).mapDerivedCategoryFactors.inv.app K) := by
  have h := rightDerivedFunctorMapOfNatIsoCompForgetIso_hom_fac e
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app] at h
  have c₁ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (mapOfNatIso e ⋙ forget G))
      (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient (IsoAlgebra F) (ComplexShape.up ℤ)).obj K) = 𝟙 _ := rfl
  have c₂ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (forget F ⋙ L))
      (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient (IsoAlgebra F) (ComplexShape.up ℤ)).obj K) = 𝟙 _ := rfl
  have c₃ : (NatTrans.mapHomotopyCategory (mapOfNatIsoCompForgetIso e).hom
      (ComplexShape.up ℤ)).app
        ((HomotopyCategory.quotient (IsoAlgebra F) (ComplexShape.up ℤ)).obj K) = 𝟙 _ := by
    simp [mapOfNatIsoCompForgetIso]
  simp only [c₁, c₂, c₃, Functor.map_id, Category.id_comp, Category.assoc] at h
  erw [Functor.mapDerivedCategoryFactorsh_inv_app_quotient_obj,
    Functor.mapDerivedCategoryFactorsh_inv_app_quotient_obj] at h
  rw [Functor.rightDerivedFunctorUnitQ_eq_rightDerivedFunctorUnit_app,
    Functor.rightDerivedFunctorUnitQ_eq_rightDerivedFunctorUnit_app]
  exact h

omit [HasColimitsOfShape (Discrete ℤ) D] [HasExactColimitsOfShape (Discrete ℤ) D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)] in
/-- The inverse form of
`mapDerivedCategoryFactors_inv_app_comp_rightDerivedFunctorMapOfNatIsoCompForgetIso_hom`. -/
@[reassoc]
lemma rightDerivedFunctorUnitQ_comp_rightDerivedFunctorMapOfNatIsoCompForgetIso_inv
    (K : CochainComplex (IsoAlgebra F) ℤ) :
    L.rightDerivedFunctorUnitQ (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        L.rightDerivedFunctor.map ((forget F).mapDerivedCategoryFactors.inv.app K) ≫
        (rightDerivedFunctorMapOfNatIsoCompForgetIso F e).inv.app (DerivedCategory.Q.obj K) =
      (forget G).mapDerivedCategoryFactors.inv.app
          (((mapOfNatIso e).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (forget G).mapDerivedCategory.map ((mapOfNatIso e).rightDerivedFunctorUnitQ K) := by
  rw [← Category.assoc,
    ← mapDerivedCategoryFactors_inv_app_comp_rightDerivedFunctorMapOfNatIsoCompForgetIso_hom e K]
  simp

omit [HasColimitsOfShape (Discrete ℤ) D] [HasExactColimitsOfShape (Discrete ℤ) D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)] in
/-- The unit of `R(mapOfNatIso e)` is an isomorphism at a complex of algebras `K` as soon as
the unit of `RL` is an isomorphism at the underlying complex of `K`. -/
lemma isIso_rightDerivedFunctorUnitQ_mapOfNatIso (K : CochainComplex (IsoAlgebra F) ℤ)
    [IsIso (L.rightDerivedFunctorUnitQ
      (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))] :
    IsIso ((mapOfNatIso e).rightDerivedFunctorUnitQ K) := by
  have h : IsIso ((forget G).mapDerivedCategoryFactors.inv.app
        (((mapOfNatIso e).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (forget G).mapDerivedCategory.map ((mapOfNatIso e).rightDerivedFunctorUnitQ K) ≫
      (rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app (DerivedCategory.Q.obj K)) := by
    rw [mapDerivedCategoryFactors_inv_app_comp_rightDerivedFunctorMapOfNatIsoCompForgetIso_hom]
    infer_instance
  have := IsIso.of_isIso_comp_left ((forget G).mapDerivedCategoryFactors.inv.app
    (((mapOfNatIso e).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    ((forget G).mapDerivedCategory.map ((mapOfNatIso e).rightDerivedFunctorUnitQ K) ≫
      (rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app (DerivedCategory.Q.obj K))
  have := IsIso.of_isIso_comp_right
    ((forget G).mapDerivedCategory.map ((mapOfNatIso e).rightDerivedFunctorUnitQ K))
    ((rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app (DerivedCategory.Q.obj K))
  exact isIso_of_isIso_forget_mapDerivedCategory_map _

omit [Abelian.HasKInjectiveResolutions (IsoAlgebra G)] in
/-- **Right derived transports commute with free algebras.** Let `I` be a K-injective complex
such that `L` preserves the coproducts `∐ₙ Fⁿ Iᵏ` and the unit of `RL` is an isomorphism at the
complex `∐ₙ Fⁿ I` underlying the free algebra on `I`. Then the free comparison
`D(Free)(RL (Q I)) ⟶ R(mapOfNatIso e)(D(Free) (Q I))` is an isomorphism. -/
theorem isIso_freeComparison_rightDerivedFunctor (I : CochainComplex C ℤ) [I.IsKInjective]
    [∀ k, PreservesColimit (Discrete.functor (Free.obj F (I.X k))) L]
    (hI : IsIso (L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj
      (((Free.functor F ⋙ forget F).mapHomologicalComplex (.up ℤ)).obj I)))) :
    IsIso (Adjunction.freeComparison (Free.adjunction F).mapExactDerivedCategory
      (Free.adjunction G).mapExactDerivedCategory (mapOfNatIso e).rightDerivedFunctor
      L.rightDerivedFunctor (rightDerivedFunctorMapOfNatIsoCompForgetIso F e)
      (DerivedCategory.Q.obj I)) := by
  let β := Adjunction.freeComparisonNatTrans (Free.adjunction F) (Free.adjunction G)
    (mapOfNatIso e) L (mapOfNatIsoCompForgetIso e)
  let J := ((Free.functor F).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have : ∀ k, IsIso (((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I).f k) :=
    fun k ↦ isIso_freeComparison_mapOfNatIso e (I.X k)
  have : IsIso ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (L.rightDerivedFunctorUnitQ
      (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) := by
    rw [Functor.rightDerivedFunctorUnitQ_eq_rightDerivedFunctorUnit_app]
    exact hI
  have := isIso_rightDerivedFunctorUnitQ_mapOfNatIso e J
  -- the free comparison is the composite
  -- `D(Free)(RL (Q I)) ≅ Q(Free (L I)) ≅ Q(mapOfNatIso e (Free I)) ≅ R(mapOfNatIso e)(Q(Free I))`
  have key : Adjunction.freeComparison (Free.adjunction F).mapExactDerivedCategory
      (Free.adjunction G).mapExactDerivedCategory (mapOfNatIso e).rightDerivedFunctor
      L.rightDerivedFunctor (rightDerivedFunctorMapOfNatIsoCompForgetIso F e)
      (DerivedCategory.Q.obj I) =
    (Free.functor G).mapDerivedCategory.map (inv (L.rightDerivedFunctorUnitQ I)) ≫
      (Free.functor G).mapDerivedCategoryFactors.hom.app
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I) ≫
      (mapOfNatIso e).rightDerivedFunctorUnitQ J ≫
      (mapOfNatIso e).rightDerivedFunctor.map
        ((Free.functor F).mapDerivedCategoryFactors.inv.app I) := by
    rw [Adjunction.freeComparison, Equiv.symm_apply_eq, Adjunction.homEquiv_unit,
      ← cancel_epi (L.rightDerivedFunctorUnitQ I)]
    have hu : L.rightDerivedFunctorUnitQ I ≫
        (Free.adjunction G).mapExactDerivedCategory.unit.app
          (L.rightDerivedFunctor.obj (DerivedCategory.Q.obj I)) ≫
        (forget G).mapDerivedCategory.map ((Free.functor G).mapDerivedCategory.map
          (inv (L.rightDerivedFunctorUnitQ I))) =
        (Free.adjunction G).mapExactDerivedCategory.unit.app
          (DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
      rw [← Adjunction.unit_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp,
        IsIso.hom_inv_id, Functor.map_id, Functor.map_id, Category.comp_id]
    rw [Functor.map_comp, reassoc_of% hu, Adjunction.localization_unit_app,
      Adjunction.localization_unit_app]
    simp only [CatCommSq.iso, Iso.symm_hom]
    have hc := (rightDerivedFunctorMapOfNatIsoCompForgetIso F e).inv.naturality
      ((Free.functor F).mapDerivedCategoryFactors.inv.app I)
    have hf := (forget G).mapDerivedCategoryFactors.inv.naturality
      ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I)
    simp only [Functor.comp_map, Functor.comp_obj] at hc hf
    simp only [Functor.map_comp, Category.assoc]
    rw [hc, ← Functor.rightDerivedFunctorUnitQ_naturality_assoc]
    simp only [Functor.comp_obj]
    rw [rightDerivedFunctorUnitQ_comp_rightDerivedFunctorMapOfNatIsoCompForgetIso_inv_assoc,
      ← Functor.map_comp_assoc (forget G).mapDerivedCategory
        ((Free.functor G).mapDerivedCategoryFactors.inv.app _), Iso.inv_hom_id_app,
      Functor.map_id, Category.id_comp]
    erw [← reassoc_of% hf]
    rw [← Functor.map_comp_assoc]
    -- termwise, `η_{L S} ≫ For (β_S) = L (η_S)`
    congr 2
    ext k
    have h := Adjunction.unit_app_comp_map_freeComparison (Free.adjunction F)
      (Free.adjunction G) (mapOfNatIso e) L (mapOfNatIsoCompForgetIso e) (I.X k)
    simp only [Adjunction.mapHomologicalComplex, Functor.id_obj, Functor.comp_obj,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, Adjunction.freeComparisonNatTrans_app, forget_map, β]
    refine (h.trans ?_).symm
    simp [mapOfNatIsoCompForgetIso]
  rw [key]
  infer_instance

end CategoryTheory.Endofunctor.IsoAlgebra
