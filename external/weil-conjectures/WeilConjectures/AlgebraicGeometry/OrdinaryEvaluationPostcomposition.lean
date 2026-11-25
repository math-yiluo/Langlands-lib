/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationComponentFactorization

/-! # Ordinary evaluation postcomposition

Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-ordinary-evaluation-postcomposition).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

private theorem hom_ext_local (X : Scheme.{u}) (U : X.Opens) (n : ℤ)
    {A B : CochainComplex (localEvaluationModules X U) ℤ}
    {S : localEvaluationModules X U} {a b : S ⟶ (homComplex (R := X.sheaf.over U) A B).X n}
    (h : ∀ p : ℤ, a ≫ localEvaluationProjection X U A B n p (p + n) rfl =
      b ≫ localEvaluationProjection X U A B n p (p + n) rfl) : a = b := by
  let hlim := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := X.sheaf.over U))).1 A B n
  apply hlim.some.hom_ext
  intro p
  exact h p.as

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

@[reassoc] private theorem evaluation_postcomposition {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (E B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (a : B ⟶ B') :
    a ▷ SheafOfModules.homObj (R := R) E (𝟙_ _) ≫
        SheafOfModules.moduleDualEvaluation R E B' =
      SheafOfModules.moduleDualEvaluation R E B ≫
        SheafOfModules.homObjMap (R := R) (𝟙 E) a := by
  unfold SheafOfModules.moduleDualEvaluation
  rw [← SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := R),
    ← SheafOfModules.tensorHomEquiv_comp_homObjMap (R := R)]
  apply (SheafOfModules.tensorHomEquiv (R := R) E _ B').congr_arg
  rw [BraidedCategory.braiding_naturality_right_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
private theorem projection_postcomposition (X : Scheme.{u}) (U : X.Opens)
    (P F F' : CochainComplex (localEvaluationModules X U) ℤ) (t : F ⟶ F') (n p : ℤ) :
    (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t).f n ≫
      localEvaluationProjection X U P F' n p (p + n) rfl =
    localEvaluationProjection X U P F n p (p + n) rfl ≫
      SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X p)) (t.f (p + n)) := by
  have hm := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := X.sheaf.over U))).2.2
      P P F F' (𝟙 P) t n p (p + n) rfl
  simpa only [localEvaluationProjection, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, HomologicalComplex.id_f] using hm

set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryEvaluation_component_postcomposition (X : Scheme.{u}) (U : X.Opens)
    (P F F' : CochainComplex (localEvaluationModules X U) ℤ) (t : F ⟶ F')
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (f' : localEvaluationTensor X U P F' ⟶ homComplex (R := X.sheaf.over U) P F')
    (hf : IsLocalOrdinaryEvaluation X U P F f)
    (hf' : IsLocalOrdinaryEvaluation X U P F' f') (n p i j : ℤ)
    (hij : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, j) = n) :
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) i j n hij ≫ (HomologicalComplex.mapBifunctorMap t
        (𝟙 (localEvaluationDual X U P)) (curriedTensor _) (.up ℤ)).f n ≫ f'.f n ≫
        localEvaluationProjection X U P F' n p (p + n) rfl =
      HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) i j n hij ≫ f.f n ≫
        (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t).f n ≫
        localEvaluationProjection X U P F' n p (p + n) rfl := by
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, Category.id_comp, curriedTensor_map_app]
  simp only [hf' i j n p hij, projection_postcomposition X U P F F' t n p,
    reassoc_of% (hf i j n p hij)]
  by_cases hr : p + j = 0
  · simp only [ordinaryEvaluation_component_factorization X U P F' i j n p hij hr,
      ordinaryEvaluation_component_factorization X U P F i j n p hij hr]
    simp only [← whisker_exchange_assoc (t.f i), evaluation_postcomposition_assoc.{u}
      (C := Over U) (J := (Opens.grothendieckTopology X).over U)
      (X.sheaf.over U) (P.X p) (F.X i) (F'.X i) (t.f i),
      Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
      Category.id_comp, HomologicalComplex.XIsoOfEq_hom_naturality]
  · simp only [localEvaluationComponent, dite_eq_right hr, comp_zero,
      zero_comp]

/-- Ordinary evaluation is natural in the coefficient complex.
Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom) and
Tag 08DQ (lemma-dual-perfect-complex), component calculation.
(blueprint: lem-pc-ordinary-evaluation-postcomposition).

Proof: Use chain-map extensionality, total tensor coproduct inclusions in degrees
(p,q), and the Hom product projections indexed by r. Naturality of tensor inclusions
changes the source coefficient by t.f p. Naturality of the Hom projection changes
the target by t.f (r+n). Substitute hf and hf' on the two sides. When r+q is nonzero
both components vanish. Otherwise expand localEvaluationComponent. Naturality of
the tensor-Hom equivalence, associator, braiding and right unitor moves t.f p
through evaluation. The chain-object transport to degree r+n is natural, so the
components agree. The projections and inclusions are jointly detecting. -/
theorem ordinaryEvaluation_postcomposition (X : Scheme.{u}) (U : X.Opens)
    (P F F' : CochainComplex (localEvaluationModules X U) ℤ) (t : F ⟶ F')
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (f' : localEvaluationTensor X U P F' ⟶ homComplex (R := X.sheaf.over U) P F')
    (hf : IsLocalOrdinaryEvaluation X U P F f)
    (hf' : IsLocalOrdinaryEvaluation X U P F' f') :
    HomologicalComplex.mapBifunctorMap t (𝟙 (localEvaluationDual X U P))
      (curriedTensor _) (.up ℤ) ≫ f' =
        f ≫ ((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t := by
  apply HomologicalComplex.hom_ext
  intro n
  apply hom_ext_local X U n
  intro p
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  exact ordinaryEvaluation_component_postcomposition X U P F F' t f f' hf hf' n p i j hij

end AlgebraicGeometry
