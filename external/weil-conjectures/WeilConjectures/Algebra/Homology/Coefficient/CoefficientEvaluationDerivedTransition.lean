/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedCore
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientScalarDerivedAdjunction
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Localizing the transitions of coefficient systems

Source: Zheng, Construction 4.1, p. 21, the transition morphisms of a complex of systems.
(blueprint: lem-pur-coefficient-evaluation-derived-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w d
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
private theorem localization_comparison_cancel
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {X Y : A} {Z U V : B} (j : X ≅ Y) (i : R.obj Y ≅ Z)
    (a : U ⟶ V) (b : V ⟶ Z) :
    (a ≫ b ≫ 𝟙 Z ≫ i.inv ≫ 𝟙 (R.obj Y) ≫ R.map j.inv ≫ 𝟙 (R.obj X)) ≫
        R.map j.hom ≫ i.hom = a ≫ b := by
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← R.map_comp_assoc, j.inv_hom_id, R.map_id, Category.id_comp,
    i.inv_hom_id, Category.comp_id]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Strict system transitions descend with their specified comparison equation.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-transition).
Proof: conjugate the termwise strict transition by the evaluation and scalar-restriction
localization comparisons. This is a natural transformation between the composites of
the required derived functors with localization. Precomposition with localization is
fully faithful, so it uniquely descends to the derived category. Evaluate the defining
preimage equation at a complex and cancel the two comparison isomorphisms; this gives
the asserted representative formula. -/
theorem coefficientEvaluationDerivedTransition
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (core : CoefficientEvaluationDerivedCoreData ordinary) {m n : ℕ} (h : n ≤ m) :
    ∃ t : core.evaluation m ⟶ core.evaluation n ⋙ (scalar h).restriction,
      ∀ K, t.app (DerivedCategory.Q.obj K) ≫
        (scalar h).restriction.map ((core.evaluationFactors n).hom.app K) ≫
        (scalar h).restrictionFactors.hom.app
          (((coefficientEvaluation (J := J) (O := O) (ell := ell) n).mapHomologicalComplex
            (.up ℤ)).obj K) =
        (core.evaluationFactors m).hom.app K ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinary.strictTransition h) (.up ℤ)).app K) := by
  let e k := (coefficientEvaluation (J := J) (O := O) (ell := ell) k).mapHomologicalComplex
    (.up ℤ)
  let R := (scalar h).restriction
  let r := (coefficientRestriction (J := J) O ell h).mapHomologicalComplex (.up ℤ)
  let t : e m ⟶ e n ⋙ r :=
    NatTrans.mapHomologicalComplex (ordinary.strictTransition h) (.up ℤ)
  let α : DerivedCategory.Q ⋙ core.evaluation m ⟶
      DerivedCategory.Q ⋙ (core.evaluation n ⋙ R) :=
    (core.evaluationFactors m).hom ≫
      CategoryTheory.Functor.whiskerRight t DerivedCategory.Q ≫
      (CategoryTheory.Functor.associator (e n) r DerivedCategory.Q).hom ≫
      CategoryTheory.Functor.whiskerLeft (e n) (scalar h).restrictionFactors.inv ≫
      (CategoryTheory.Functor.associator (e n) DerivedCategory.Q R).inv ≫
      CategoryTheory.Functor.whiskerRight (core.evaluationFactors n).inv R ≫
      (CategoryTheory.Functor.associator DerivedCategory.Q (core.evaluation n) R).hom
  let F := Localization.whiskeringLeftFunctor' DerivedCategory.Q
    (HomologicalComplex.quasiIso (CoefficientSystem (J := J) O ell) (.up ℤ))
    (DerivedCategory (coefficientLevelModules (J := J) O ell m))
  let τ := F.preimage α
  refine ⟨τ, ?_⟩
  intro K
  have ht : τ.app (DerivedCategory.Q.obj K) = α.app K :=
    congr_app (F.map_preimage α) K
  rw [ht]
  dsimp only [α, NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.whiskerLeft_app,
    CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.associator_inv_app]
  exact localization_comparison_cancel R ((core.evaluationFactors n).app K)
    ((scalar h).restrictionFactors.app ((e n).obj K))
    ((core.evaluationFactors m).hom.app K) (DerivedCategory.Q.map (t.app K))

end SheafOfModules
