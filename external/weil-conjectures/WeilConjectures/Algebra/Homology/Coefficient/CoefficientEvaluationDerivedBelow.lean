/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedCore
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientScalarDerivedAdjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Evaluation of a derived extension below its defining level

Source: Zheng, Construction 4.1, p. 21; Stacks Project, Tag 06XN.
(blueprint: lem-pur-coefficient-evaluation-derived-below).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w d
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
private theorem three_identity_compositions
    {A : Type*} [Category A] {W X Y Z : A}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    𝟙 W ≫ a ≫ 𝟙 X ≫ b ≫ 𝟙 Y ≫ c = a ≫ b ≫ c := by
  simp only [Category.id_comp]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evaluation of the derived extension below its level is derived scalar extension,
with the comparison induced by the ordinary below-level formula on complexes.
Source: Zheng, Construction 4.1, p. 21; Stacks Project, Tag 06XN
(blueprint: lem-pur-coefficient-evaluation-derived-below).
Proof: derived evaluation is a right adjoint, so it preserves the limits defining the
pointwise right Kan extension of the ordinary extension functor. Postcompose that Kan
extension by evaluation. The evaluation localization comparison and the ordinary
below-level tensor isomorphism identify its input functor with termwise scalar extension
followed by localization. Uniqueness of left derived functors gives the comparison
isomorphism. Its defining counit equation, precomposed with its inverse, is exactly the
stated equation on complex representatives. -/
theorem coefficientEvaluationDerivedBelow
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (core : CoefficientEvaluationDerivedCoreData ordinary) {n q : ℕ} (h : q ≤ n) :
    ∃ i : core.derivedExtension n ⋙ core.evaluation q ≅ (scalar h).derived,
      ∀ P, i.inv.app (DerivedCategory.Q.obj P) ≫
        (core.evaluation q).map ((core.counit n).app P) ≫
        (core.evaluationFactors q).hom.app
          (((ordinary.extension n).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinary.below h) (.up ℤ)).hom.app P) =
          (scalar h).counit.app P := by
  let E := (ordinary.extension n).mapHomologicalComplex (.up ℤ)
  let e := (coefficientEvaluation (J := J) (O := O) (ell := ell) q).mapHomologicalComplex
    (.up ℤ)
  let T := (coefficientTensor (J := J) (O := O) (ell := ell) h).mapHomologicalComplex (.up ℤ)
  let F := E ⋙ DerivedCategory.Q
  let G := core.evaluation q
  let L := core.derivedExtension n ⋙ G
  let W := HomologicalComplex.quasiIso (coefficientLevelModules (J := J) O ell n) (.up ℤ)
  let α : DerivedCategory.Q ⋙ L ⟶ F ⋙ G :=
    (CategoryTheory.Functor.associator _ _ _).inv ≫
      CategoryTheory.Functor.whiskerRight (core.counit n) G
  let := core.isDerived n
  let := CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension
    (core.derivedExtension n) (core.counit n) W
  let := core.pointwise n
  let := F.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor DerivedCategory.Q W
  let := (core.derivedAdj q).isRightAdjoint
  have : L.IsLeftDerivedFunctor α W :=
    ⟨CategoryTheory.Functor.PreservesRightKanExtension.preserves
      (G := G) (core.derivedExtension n) (core.counit n)⟩
  let b : E ⋙ e ≅ T := NatIso.mapHomologicalComplex (ordinary.below h) (.up ℤ)
  let τ : F ⋙ G ≅ T ⋙ DerivedCategory.Q :=
    CategoryTheory.Functor.associator E DerivedCategory.Q G ≪≫
      CategoryTheory.Functor.isoWhiskerLeft E (core.evaluationFactors q) ≪≫
      (CategoryTheory.Functor.associator E e DerivedCategory.Q).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight b DerivedCategory.Q
  let := (scalar h).isDerived
  let i := CategoryTheory.Functor.leftDerivedNatIso L (scalar h).derived
    α (scalar h).counit W τ
  refine ⟨i, ?_⟩
  intro P
  have hi := CategoryTheory.Functor.leftDerivedNatTrans_app
    L (scalar h).derived α (scalar h).counit W τ.hom P
  change i.hom.app (DerivedCategory.Q.obj P) ≫ (scalar h).counit.app P =
    α.app P ≫ τ.hom.app P at hi
  apply (cancel_epi (i.hom.app (DerivedCategory.Q.obj P))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  erw [hi]
  dsimp only [α, τ, NatTrans.comp_app, Iso.trans_hom,
    CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.associator_inv_app,
    CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.isoWhiskerLeft_hom,
    CategoryTheory.Functor.isoWhiskerRight_hom, CategoryTheory.Functor.whiskerLeft_app]
  dsimp only [Iso.symm_hom, CategoryTheory.Functor.associator_inv_app]
  simp only [Category.assoc]
  exact (three_identity_compositions (G.map ((core.counit n).app P))
    ((core.evaluationFactors q).hom.app (E.obj P))
    (DerivedCategory.Q.map (b.hom.app P))).symm

end SheafOfModules
