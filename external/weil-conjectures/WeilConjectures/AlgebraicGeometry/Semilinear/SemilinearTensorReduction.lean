/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorComparisons
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction
import all WeilConjectures.AlgebraicGeometry.System.SystemCochainTensorReduction
import all WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula
import WeilConjectures.AlgebraicGeometry.System.SystemEvaluationFlat

/-! # Reduction compatibility for semilinear tensor models

## References

* Zheng Construction 4.1 and Stacks 07A4, 08J9
* Stacks 06YN
-/
@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

namespace TensorReductionProof
-- Adapt the ordinary, cochain and derived proofs in SystemOrdinaryTensorReduction,
-- SystemCochainTensorReduction and SystemTensorReductionFormula to the supplied
-- scalar/tensor components. Their generic proof helpers are reused through private imports.
attribute [local irreducible] hasDerived SheafOfModules.monoidalCategory evaluation
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private def ordinaryReduction (S : SystemScalarCoherence.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ) :
    (S.scalar h).model.E.obj ((evaluation.{c, v, max c v r} J B τ m).obj M) ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj M :=
  ((S.scalar h).ordinaryAdjunction.homEquiv _ _).symm
    ((transition.{c, v, max c v r} J B τ h).app M)

private theorem ordinary_tensor_reduction (S : SystemScalarCoherence.{c, v, r} J B τ)
    (A : SystemTensorBase.{c, v, r} J B τ)
    (T : SystemTensorComparisons.{c, v, r} J B τ S A) {m n : ℕ}
    (h : n ≤ m) (M N : Systems.{c, v, max c v r} J B τ) :
    ordinaryReduction.{c, v, r} J B τ S h
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) ≫
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom =
    (S.scalar h).model.E.map
        (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).hom ≫
      ((T.scalarTensorModel h).ordinary
        ((evaluation.{c, v, max c v r} J B τ m).obj M)
        ((evaluation.{c, v, max c v r} J B τ m).obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J (B n)
        (ordinaryReduction.{c, v, r} J B τ S h M)
        (ordinaryReduction.{c, v, r} J B τ S h N) := by
  apply ((S.scalar h).ordinaryAdjunction.homEquiv _ _).injective
  rw [(S.scalar h).ordinaryAdjunction.homEquiv_naturality_right,
    (S.scalar h).ordinaryAdjunction.homEquiv_naturality_left]
  simp only [ordinaryReduction, Equiv.apply_symm_apply]
  apply (cancel_epi (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply tensor_hom_ext.{c, v, r} J
  intro U x y
  obtain ⟨x, rfl⟩ := evalSection_surjective.{c, v, r} J B τ m M U x
  obtain ⟨y, rfl⟩ := evalSection_surjective.{c, v, r} J B τ m N U y
  change (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
    (((transition.{c, v, max c v r} J B τ h).app _).val.app U
      ((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U
        (tensorSection.{c, v, r} J (B m) _ _ U _ _))) = _
  rw [evaluation_inv_pure_cast.{c, v, r} J B τ m M N U x y]
  rw [transition_apply_cast.{c, v, r} J B τ h
    (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) M N) U]
  rw [tensorSection_restrict.{c, v, r} (coefficientSequenceTopology J)
    (R := systemRing.{c, v, max c v r} J B τ) M N
    (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x y]
  erw [evaluation_pure_cast.{c, v, r} J B τ n M N U
    (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
    (N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op y)]
  have ht := scalar_tensor_transpose_section.{c, v, r} J (coefficientMap J B τ h)
    (S.scalar h) (T.scalarTensorModel h).ordinary (T.scalarTensorModel h).ordinary_pure
    ((evaluation.{c, v, max c v r} J B τ m).obj M)
    ((evaluation.{c, v, max c v r} J B τ m).obj N)
    ((evaluation.{c, v, max c v r} J B τ n).obj M)
    ((evaluation.{c, v, max c v r} J B τ n).obj N)
    (ordinaryReduction.{c, v, r} J B τ S h M)
    (ordinaryReduction.{c, v, r} J B τ S h N) U
    (evalSection.{c, v, r} J B τ m M U x) (evalSection.{c, v, r} J B τ m N U y)
  simp only [ordinaryReduction, Equiv.apply_symm_apply] at ht
  have hx := transition_apply_cast.{c, v, r} J B τ h M U x
  have hy := transition_apply_cast.{c, v, r} J B τ h N U y
  erw [hx, hy] at ht
  exact ht.symm

private def cochainReduction (S : SystemScalarCoherence.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    ((S.scalar h).model.E.mapHomologicalComplex (.up ℤ)).obj
      (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P where
  f k := ordinaryReduction.{c, v, r} J B τ S h (P.X k)
  comm' k l := by
    intro _
    symm
    change (S.scalar h).model.E.map
        ((evaluation.{c, v, max c v r} J B τ m).map (P.d k l)) ≫
        ordinaryReduction.{c, v, r} J B τ S h (P.X l) =
      ordinaryReduction.{c, v, r} J B τ S h (P.X k) ≫
        (evaluation.{c, v, max c v r} J B τ n).map (P.d k l)
    apply ((S.scalar h).ordinaryAdjunction.homEquiv _ _).injective
    rw [(S.scalar h).ordinaryAdjunction.homEquiv_naturality_left,
      (S.scalar h).ordinaryAdjunction.homEquiv_naturality_right]
    simp only [ordinaryReduction, Equiv.apply_symm_apply]
    exact (transition.{c, v, max c v r} J B τ h).naturality (P.d k l)

private theorem cochainReduction_f (S : SystemScalarCoherence.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) (k : ℤ) :
    (cochainReduction.{c, v, r} J B τ S h P).f k =
      ordinaryReduction.{c, v, r} J B τ S h (P.X k) := rfl

/-- The degreewise construction agrees with the induced cochain adjunction. -/
private theorem cochainReduction_eq_transpose (S : SystemScalarCoherence.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    cochainReduction.{c, v, r} J B τ S h P =
      (((S.scalar h).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
        ((NatTrans.mapHomologicalComplex
          (transition.{c, v, max c v r} J B τ h) (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (evaluation.{c, v, max c v r} J B τ n ⋙
              res (coefficientMap J B τ h))) (.up ℤ)).inv.app P) := by
  apply HomologicalComplex.Hom.ext
  funext k
  rw [Adjunction.homEquiv_counit]
  change ordinaryReduction.{c, v, r} J B τ S h (P.X k) = _
  rw [ordinaryReduction, Adjunction.homEquiv_counit]
  rfl

private theorem ordinaryReduction_naturality (S : SystemScalarCoherence.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) {M N : Systems.{c, v, max c v r} J B τ} (f : M ⟶ N) :
    (S.scalar h).model.E.map ((evaluation.{c, v, max c v r} J B τ m).map f) ≫
      ordinaryReduction.{c, v, r} J B τ S h N =
    ordinaryReduction.{c, v, r} J B τ S h M ≫
      (evaluation.{c, v, max c v r} J B τ n).map f := by
  apply ((S.scalar h).ordinaryAdjunction.homEquiv _ _).injective
  rw [(S.scalar h).ordinaryAdjunction.homEquiv_naturality_left,
    (S.scalar h).ordinaryAdjunction.homEquiv_naturality_right]
  simp only [ordinaryReduction, Equiv.apply_symm_apply]
  exact (transition.{c, v, max c v r} J B τ h).naturality f

private theorem ordinary_tensor_reduction_inv (S : SystemScalarCoherence.{c, v, r} J B τ)
    (A : SystemTensorBase.{c, v, r} J B τ)
    (T : SystemTensorComparisons.{c, v, r} J B τ S A)
    {m n : ℕ} (h : n ≤ m) (M N : Systems.{c, v, max c v r} J B τ) :
    ((T.scalarTensorModel h).ordinary
        ((evaluation.{c, v, max c v r} J B τ m).obj M)
        ((evaluation.{c, v, max c v r} J B τ m).obj N)).inv ≫
      (S.scalar h).model.E.map
        (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv ≫
      ordinaryReduction.{c, v, r} J B τ S h
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) =
    ordinaryTensorHom.{c, v, r} J (B n)
        (ordinaryReduction.{c, v, r} J B τ S h M)
        (ordinaryReduction.{c, v, r} J B τ S h N) ≫
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv := by
  apply (cancel_mono (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [ordinary_tensor_reduction.{c, v, r} J B τ S A T h M N]
  rw [← (S.scalar h).model.E.map_comp_assoc, Iso.inv_hom_id]
  erw [(S.scalar h).model.E.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]

-- The total-summand identity crosses three dependent ringed module categories.
private theorem cochain_tensor_reduction (S : SystemScalarCoherence.{c, v, r} J B τ)
    (A : SystemTensorBase.{c, v, r} J B τ)
    (T : SystemTensorComparisons.{c, v, r} J B τ S A) {m n : ℕ} (h : n ≤ m)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    (T.scalarTensorModel h).chain
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P)
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      ((S.scalar h).model.E.mapHomologicalComplex (.up ℤ)).map
        ((T.tensorEvaluationModel m).chain P Q) ≫
      cochainReduction.{c, v, r} J B τ S h
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)).obj (P, Q)) =
    (totalTensor.{c, v, r} J (B n)).map
        (Prod.mkHom (cochainReduction.{c, v, r} J B τ S h P)
          (cochainReduction.{c, v, r} J B τ S h Q)) ≫
      (T.tensorEvaluationModel n).chain P Q := by
  apply HomologicalComplex.Hom.ext
  funext k
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B n)
  let := SheafOfModules.monoidalCategory (B n)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients (B n)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients (B n)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  let Pm := ((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P
  let Qm := ((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj Q
  have hs := (T.scalarTensorModel h).summand Pm Qm p q k hpq
  have hm := (T.tensorEvaluationModel m).summand P Q p q k hpq
  have hn := (T.tensorEvaluationModel n).summand P Q p q k hpq
  have hmap := tensorSummand_map.{c, v, r} J (B n)
    (cochainReduction.{c, v, r} J B τ S h P)
    (cochainReduction.{c, v, r} J B τ S h Q) p q k hpq
  have hnat := ordinaryReduction_naturality.{c, v, r} J B τ S h
    (tensorSummand.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P Q p q k hpq)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change tensorSummand.{c, v, r} J (B n)
      (((S.scalar h).model.E.mapHomologicalComplex (.up ℤ)).obj Pm)
      (((S.scalar h).model.E.mapHomologicalComplex (.up ℤ)).obj Qm)
      p q k hpq ≫ _ = _
  rw [T.tensorEvaluationModel_ordinary m (P.X p) (Q.X q)] at hm
  rw [T.tensorEvaluationModel_ordinary n (P.X p) (Q.X q)] at hn
  exact cochainReduction_summand_paste (S.scalar h).model.E hs hm hn hmap hnat
    (ordinary_tensor_reduction_inv.{c, v, r} J B τ S A T h (P.X p) (Q.X q))

private theorem reduction_naturality (S : SystemScalarCoherence.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) {P Q : DS.{c, v, max c v r} J B τ} (f : P ⟶ Q) :
    (S.scalar h).T.map ((e.{c, v, max c v r} J B τ m).map f) ≫ reduction J B τ h (S.scalar h) Q =
      reduction J B τ h (S.scalar h) P ≫ (e J B τ n).map f := by
  apply ((S.scalar h).adjunction.homEquiv _ _).injective
  rw [(S.scalar h).adjunction.homEquiv_naturality_left,
    (S.scalar h).adjunction.homEquiv_naturality_right]
  simp only [reduction, Equiv.apply_symm_apply]
  exact (derivedTransition J B τ h).naturality f

private theorem reduction_on_kflat_evaluation (S : SystemScalarCoherence.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := B m)
      (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P)) :
    reduction.{c, v, max c v r} J B τ h (S.scalar h) (DerivedCategory.Q.obj P) ≫
        (Functor.mapDerivedCategoryFactors (evaluation.{c, v, max c v r} J B τ n)).hom.app P =
      (S.scalar h).T.map
          ((Functor.mapDerivedCategoryFactors (evaluation.{c, v, max c v r} J B τ m)).hom.app P) ≫
        (S.scalar h).model.ε.app
          (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((((S.scalar h).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
            ((NatTrans.mapHomologicalComplex
              (transition.{c, v, max c v r} J B τ h) (.up ℤ)).app P ≫
              (Functor.mapHomologicalComplexCompIso
                (Iso.refl (evaluation.{c, v, max c v r} J B τ n ⋙
                  res (coefficientMap J B τ h))) (.up ℤ)).inv.app P)) := by
  apply ((S.scalar h).adjunction.homEquiv _ _).injective
  rw [(S.scalar h).adjunction.homEquiv_naturality_right]
  simp only [reduction, Equiv.apply_symm_apply]
  rw [(S.scalar h).adjunction.homEquiv_naturality_left]
  apply (cancel_mono
    ((Functor.mapDerivedCategoryFactors
      (res.{c, v, max c v r} (coefficientMap J B τ h))).hom.app
        (((evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P))).1
  simp only [Category.assoc]
  let Pm := ((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P
  let Pn := ((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P
  let δ := (NatTrans.mapHomologicalComplex
    (transition.{c, v, max c v r} J B τ h) (.up ℤ)).app P ≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (evaluation.{c, v, max c v r} J B τ n ⋙
          res (coefficientMap J B τ h))) (.up ℤ)).inv.app P
  have ht := (S.scalar h).transpose_model Pm Pn hP
    ((((S.scalar h).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm δ)
  simp only [Equiv.apply_symm_apply] at ht
  dsimp only [Functor.comp_obj]
  conv_rhs => rw [ht]
  simpa only [derivedTransition, NatTrans.comp_app, Category.assoc, δ] using
    localized_transition_fac
      (evaluation.{c, v, max c v r} J B τ m)
      (evaluation.{c, v, max c v r} J B τ n)
      (res.{c, v, max c v r} (coefficientMap J B τ h))
      (transition.{c, v, max c v r} J B τ h) P

private theorem tensor_reduction_on_representatives (S : SystemScalarCoherence.{c, v, r} J B τ)
    (A : SystemTensorBase.{c, v, r} J B τ)
    (T : SystemTensorComparisons.{c, v, r} J B τ S A)
    {m n : ℕ} (h : n ≤ m)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := coefficientSequenceTopology J) (R := systemRing J B τ) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := coefficientSequenceTopology J) (R := systemRing J B τ) Q)
    (flatP : flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) P)
    (flatQ : flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) Q)
    (flatPm : flatTerms.{c, v, r} J (B m)
      (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P))
    (flatQm : flatTerms.{c, v, r} J (B m)
      (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj Q)) :
    reduction.{c, v, max c v r} J B τ h (S.scalar h)
        (A.closed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (T.tensorEvaluation n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    (S.scalar h).T.map ((T.tensorEvaluation m).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (T.scalarTensor h).hom.app
        ((e.{c, v, max c v r} J B τ m).obj (DerivedCategory.Q.obj P),
          (e.{c, v, max c v r} J B τ m).obj (DerivedCategory.Q.obj Q)) ≫
      (A.levelClosed n).tensor.map
        (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (S.scalar h)
          (DerivedCategory.Q.obj P))
          (reduction.{c, v, max c v r} J B τ h (S.scalar h) (DerivedCategory.Q.obj Q))) := by
  let F := evaluation.{c, v, max c v r} J B τ m
  let G := evaluation.{c, v, max c v r} J B τ n
  let Pm := (F.mapHomologicalComplex (.up ℤ)).obj P
  let Qm := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let Pn := (G.mapHomologicalComplex (.up ℤ)).obj P
  let Qn := (G.mapHomologicalComplex (.up ℤ)).obj Q
  let E := (S.scalar h).model.E
  let EH := E.mapHomologicalComplex (.up ℤ)
  let Tot := (totalTensor.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ)).obj (P, Q)
  let Totm := (totalTensor.{c, v, r} J (B m)).obj (Pm, Qm)
  have hPm := (T.tensorEvaluationModel m).kflat P hP flatP
  have hQm := (T.tensorEvaluationModel m).kflat Q hQ flatQ
  have hPn := (T.tensorEvaluationModel n).kflat P hP flatP
  have hQn := (T.tensorEvaluationModel n).kflat Q hQ flatQ
  have hEP := (T.scalarTensorModel h).kflat Pm hPm flatPm
  have hEQ := (T.scalarTensorModel h).kflat Qm hQm flatQm
  have hTot := coefficientTotalTensor_isKFlat.{r, c, v}
    (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) P Q hP hQ
  have flatTot := totalTensor_flatTerms.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) P Q hP hQ flatP flatQ
  have hFmTot := (T.tensorEvaluationModel m).kflat Tot hTot flatTot
  have hTotm := coefficientTotalTensor_isKFlat.{r, c, v} J (B m) Pm Qm hPm hQm
  let i := tensorModelIso.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) A.closed A.tensorModels P Q hP hQ
  let km := tensorModelIso.{c, v, r} J (B m) (A.levelClosed m) (A.levelTensorModels m)
    Pm Qm hPm hQm
  let kn := tensorModelIso.{c, v, r} J (B n) (A.levelClosed n) (A.levelTensorModels n)
    Pn Qn hPn hQn
  let kE := tensorModelIso.{c, v, r} J (B n) (A.levelClosed n) (A.levelTensorModels n)
    (EH.obj Pm) (EH.obj Qm) hEP hEQ
  let ep := scalarEpsilonIso.{c, v, r} (coefficientMap J B τ h) (S.scalar h) Pm hPm
  let eq := scalarEpsilonIso.{c, v, r} (coefficientMap J B τ h) (S.scalar h) Qm hQm
  let eT := scalarEpsilonIso.{c, v, r} (coefficientMap J B τ h) (S.scalar h)
    ((F.mapHomologicalComplex (.up ℤ)).obj Tot) hFmTot
  let eZ := scalarEpsilonIso.{c, v, r} (coefficientMap J B τ h) (S.scalar h) Totm hTotm
  let fp := F.mapDerivedCategoryFactors.app P
  let fq := F.mapDerivedCategoryFactors.app Q
  let gp := G.mapDerivedCategoryFactors.app P
  let gq := G.mapDerivedCategoryFactors.app Q
  let vm := (T.tensorEvaluation m).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  let vn := (T.tensorEvaluation n).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  let um := (e.{c, v, max c v r} J B τ m).mapIso i.symm ≪≫
    F.mapDerivedCategoryFactors.app Tot
  let un := (e.{c, v, max c v r} J B τ n).mapIso i.symm ≪≫
    G.mapDerivedCategoryFactors.app Tot
  let cm := km ≪≫ (A.levelClosed m).tensor.mapIso (fp.symm.prod fq.symm) ≪≫ vm.symm ≪≫ um
  let cn := kn ≪≫ (A.levelClosed n).tensor.mapIso (gp.symm.prod gq.symm) ≪≫ vn.symm ≪≫ un
  have hcm : cm.hom = DerivedCategory.Q.map ((T.tensorEvaluationModel m).chain P Q) := by
    simpa only [cm, um, F, Pm, Qm, Tot, km, fp, fq, vm, i, e, Iso.trans_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Category.assoc] using
      (T.tensorEvaluationModel m).derived P Q hP hQ flatP flatQ
  have hcn : cn.hom = DerivedCategory.Q.map ((T.tensorEvaluationModel n).chain P Q) := by
    simpa only [cn, un, G, Pn, Qn, Tot, kn, gp, gq, vn, i, e, Iso.trans_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Category.assoc] using
      (T.tensorEvaluationModel n).derived P Q hP hQ flatP flatQ
  refine tensor_reduction_from_model_squares
    (S.scalar h).T (A.levelClosed m).tensor (A.levelClosed n).tensor (T.scalarTensor h)
    vm vn um un km kn kE fp fq gp gq ep eq eT eZ cm cn
    (reduction.{c, v, max c v r} J B τ h (S.scalar h)
      (A.closed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
    (reduction.{c, v, max c v r} J B τ h (S.scalar h) (DerivedCategory.Q.obj P))
    (reduction.{c, v, max c v r} J B τ h (S.scalar h) (DerivedCategory.Q.obj Q))
    (DerivedCategory.Q.map (cochainReduction.{c, v, r} J B τ S h Tot))
    (DerivedCategory.Q.map (cochainReduction.{c, v, r} J B τ S h P))
    (DerivedCategory.Q.map (cochainReduction.{c, v, r} J B τ S h Q))
    (DerivedCategory.Q.map ((T.scalarTensorModel h).chain Pm Qm))
    (DerivedCategory.Q.map (EH.map ((T.tensorEvaluationModel m).chain P Q)))
    (DerivedCategory.Q.map ((totalTensor.{c, v, r} J (B n)).map
      (Prod.mkHom (cochainReduction.{c, v, r} J B τ S h P)
        (cochainReduction.{c, v, r} J B τ S h Q))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [cm, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom]
  · simp only [cn, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom]
  · exact (T.scalarTensorModel h).derived Pm Qm hPm hQm flatPm flatQm hTotm
  · have hn := reduction_naturality.{c, v, r} J B τ S h i.inv
    have ht := reduction_on_kflat_evaluation.{c, v, r} J B τ S h Tot hFmTot
    rw [← cochainReduction_eq_transpose.{c, v, r} J B τ S h Tot] at ht
    have hr₀ := congrArg
      (fun f ↦ f ≫ G.mapDerivedCategoryFactors.hom.app Tot) hn.symm
    simp only [Category.assoc] at hr₀
    have hr₁ := congrArg
      (fun f ↦ (S.scalar h).T.map ((e.{c, v, max c v r} J B τ m).map i.inv) ≫ f) ht
    simpa only [um, un, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Iso.app_hom, Functor.map_comp, Category.assoc, eT, scalarEpsilonIso, asIso_hom, F, G]
      using hr₀.trans hr₁
  · simpa only [fp, gp, ep, F, G, Pm, scalarEpsilonIso, asIso_hom, Iso.app_hom,
      ← cochainReduction_eq_transpose.{c, v, r} J B τ S h P] using
      reduction_on_kflat_evaluation.{c, v, r} J B τ S h P hPm
  · simpa only [fq, gq, eq, F, G, Qm, scalarEpsilonIso, asIso_hom, Iso.app_hom,
      ← cochainReduction_eq_transpose.{c, v, r} J B τ S h Q] using
      reduction_on_kflat_evaluation.{c, v, r} J B τ S h Q hQm
  · rw [hcm]
    simpa only [eT, eZ, scalarEpsilonIso, asIso_hom, EH, E, F, Totm, Functor.comp_map] using
      (S.scalar h).model.ε.naturality ((T.tensorEvaluationModel m).chain P Q)
  · exact (tensorModelIso_naturality.{c, v, r} J (B n) (A.levelClosed n)
      (A.levelTensorModels n) (EH.obj Pm) Pn (EH.obj Qm) Qn hEP hPn hEQ hQn
      (cochainReduction.{c, v, r} J B τ S h P)
      (cochainReduction.{c, v, r} J B τ S h Q)).symm
  · rw [hcn]
    simpa only [← Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ DerivedCategory.Q.map f) (cochain_tensor_reduction.{c, v, r} J B τ S A T h P Q)

private def reductionNat (S : SystemScalarCoherence.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m) :
    e.{c, v, max c v r} J B τ m ⋙ (S.scalar h).T ⟶ e.{c, v, max c v r} J B τ n where
  app P := reduction.{c, v, max c v r} J B τ h (S.scalar h) P
  naturality _ _ f := reduction_naturality.{c, v, r} J B τ S h f

private def tensorReductionLeft (S : SystemScalarCoherence.{c, v, r} J B τ)
    (A : SystemTensorBase.{c, v, r} J B τ)
    (T : SystemTensorComparisons.{c, v, r} J B τ S A) {m n : ℕ} (h : n ≤ m) :
    A.closed.tensor ⋙ e.{c, v, max c v r} J B τ m ⋙ (S.scalar h).T ⟶
      (e.{c, v, max c v r} J B τ n).prod (e.{c, v, max c v r} J B τ n) ⋙
        (A.levelClosed n).tensor :=
  Functor.whiskerLeft A.closed.tensor (reductionNat.{c, v, r} J B τ S h) ≫
    (T.tensorEvaluation n).hom

private def tensorReductionRight (S : SystemScalarCoherence.{c, v, r} J B τ)
    (A : SystemTensorBase.{c, v, r} J B τ)
    (T : SystemTensorComparisons.{c, v, r} J B τ S A) {m n : ℕ} (h : n ≤ m) :
    A.closed.tensor ⋙ e.{c, v, max c v r} J B τ m ⋙ (S.scalar h).T ⟶
      (e.{c, v, max c v r} J B τ n).prod (e.{c, v, max c v r} J B τ n) ⋙
        (A.levelClosed n).tensor :=
  Functor.whiskerRight (T.tensorEvaluation m).hom (S.scalar h).T ≫
    Functor.whiskerLeft ((e.{c, v, max c v r} J B τ m).prod
      (e.{c, v, max c v r} J B τ m)) (T.scalarTensor h).hom ≫
    Functor.whiskerRight ((reductionNat.{c, v, r} J B τ S h).prod
      (reductionNat.{c, v, r} J B τ S h)) (A.levelClosed n).tensor

private theorem tensor_reduction_formula (S : SystemScalarCoherence.{c, v, r} J B τ)
    (A : SystemTensorBase.{c, v, r} J B τ)
    (T : SystemTensorComparisons.{c, v, r} J B τ S A)
    (P Q : DS.{c, v, max c v r} J B τ) :
    ∀ {m n : ℕ} (h : n ≤ m),
      reduction.{c, v, max c v r} J B τ h (S.scalar h) (A.closed.tensor.obj (P, Q)) ≫
          (T.tensorEvaluation n).hom.app (P, Q) =
        (S.scalar h).T.map ((T.tensorEvaluation m).hom.app (P, Q)) ≫
          (T.scalarTensor h).hom.app
            ((e.{c, v, max c v r} J B τ m).obj P, (e.{c, v, max c v r} J B τ m).obj Q) ≫
          (A.levelClosed n).tensor.map
            (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (S.scalar h) P)
              (reduction.{c, v, max c v r} J B τ h (S.scalar h) Q)) := by
  intro m n h
  obtain ⟨P', hP, flatP, ⟨iP⟩⟩ :=
    exists_kflat_representative.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) P
  obtain ⟨Q', hQ, flatQ, ⟨iQ⟩⟩ :=
    exists_kflat_representative.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) Q
  have flatPm : flatTerms.{c, v, r} J (B m)
      (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P') := by
    intro k
    exact evaluation_preserves_flat.{c, v, r} J B τ m (P'.X k) (flatP k)
  have flatQm : flatTerms.{c, v, r} J (B m)
      (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj Q') := by
    intro k
    exact evaluation_preserves_flat.{c, v, r} J B τ m (Q'.X k) (flatQ k)
  let L := tensorReductionLeft.{c, v, r} J B τ S A T h
  let R := tensorReductionRight.{c, v, r} J B τ S A T h
  have hrep : L.app (DerivedCategory.Q.obj P', DerivedCategory.Q.obj Q') =
      R.app (DerivedCategory.Q.obj P', DerivedCategory.Q.obj Q') :=
    tensor_reduction_on_representatives.{c, v, r} J B τ S A T h P' Q' hP hQ
      flatP flatQ flatPm flatQm
  change L.app (P, Q) = R.app (P, Q)
  apply (cancel_epi
    ((A.closed.tensor ⋙ e.{c, v, max c v r} J B τ m ⋙ (S.scalar h).T).map
      (iP.prod iQ).hom)).1
  rw [L.naturality, R.naturality, hrep]

end TensorReductionProof

variable (S : SystemScalarCoherence.{c, v, r} J B τ)
/-- The strict representative equation expressing tensor/reduction compatibility. -/
theorem systemTensorReduction (A : SystemTensorBase.{c, v, r} J B τ)
    (T : SystemTensorComparisons.{c, v, r} J B τ S A) :
    ∀ {m n : ℕ} (h : n ≤ m)
    (M N : DS.{c, v, max c v r} J B τ),
    (S.scalar h).T.map ((T.tensorEvaluation m).hom.app (M, N)) ≫
        (T.scalarTensor h).hom.app
          ((e.{c, v, max c v r} J B τ m).obj M,
            (e.{c, v, max c v r} J B τ m).obj N) ≫
        (A.levelClosed n).tensor.map
          (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (S.scalar h) M)
            (reduction.{c, v, max c v r} J B τ h (S.scalar h) N)) =
      reduction.{c, v, max c v r} J B τ h (S.scalar h) (A.closed.tensor.obj (M, N)) ≫
        (T.tensorEvaluation n).hom.app (M, N) := by
  intro m n h M N
  exact (TensorReductionProof.tensor_reduction_formula.{c, v, r} J B τ S A T M N h).symm
end WeilConjectures.SemilinearSections
