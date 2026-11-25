/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.System.SystemCochainTensorReduction
import WeilConjectures.AlgebraicGeometry.System.SystemEvaluationFlat
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Tensor compatibility of the actual semilinear reductions

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 06YS, and the
horizontal restriction maps of Zheng, Construction 4.1.
(blueprint: lem-pur-system-tensor-reduction-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r

open CategoryTheory CategoryTheory.Limits

section GenericReduction
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors

section ModelFactor
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  (F : A ⥤ B) (G : A ⥤ C) (R : C ⥤ B)
  [F.Additive] [G.Additive] [R.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private theorem comp_fac_inverse (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso G R).inv.app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
    (G ⋙ R).mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ R)) (.up ℤ)).inv.app P) := by
  change _ = _ ≫ (DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ R)) (.up ℤ)).app P)).inv
  rw [Iso.eq_comp_inv]
  simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom] using
    Functor.mapDerivedCategoryCompIso_fac G R P

private theorem localized_transition_fac (δ : F ⟶ G ⋙ R) (P : CochainComplex A ℤ) :
    (Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((G ⋙ R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory (G ⋙ R).mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex δ (.up ℤ))
        DerivedCategory.Q)).app (DerivedCategory.Q.obj P) ≫
      (Functor.mapDerivedCategoryCompIso G R).inv.app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
    F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex δ (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ R)) (.up ℤ)).inv.app P) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory =
    F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
      ((G ⋙ R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (G ⋙ R).mapDerivedCategory = (G ⋙ R).mapDerivedCategoryFactors := rfl
  rw [Localization.liftNatTrans_app]
  simp only [hF, hG, Functor.whiskerRight_app, Category.assoc]
  rw [comp_fac_inverse G R P]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp]

end ModelFactor

end GenericReduction

section TensorDiagram
universe u₄ v₄ u₅ v₅

private theorem tensor_reduction_from_model_squares
    {C : Type u₄} [Category.{v₄} C] {D : Type u₅} [Category.{v₅} D]
    (S : C ⥤ D) (T : C × C ⥤ C) (T' : D × D ⥤ D)
    (μ : T ⋙ S ≅ (S.prod S) ⋙ T')
    {x p q t z a b : C} {y p' q' t' z' a' b' ea eb et ez zE : D}
    (vm : x ≅ T.obj (p, q)) (vn : y ≅ T'.obj (p', q'))
    (uModel : x ≅ t) (vModel : y ≅ t') (k : z ≅ T.obj (a, b)) (j : z' ≅ T'.obj (a', b'))
    (kE : zE ≅ T'.obj (ea, eb)) (fp : p ≅ a) (fq : q ≅ b)
    (gp : p' ≅ a') (gq : q' ≅ b')
    (ep : S.obj a ≅ ea) (eq : S.obj b ≅ eb)
    (eT : S.obj t ≅ et) (eZ : S.obj z ≅ ez)
    (cm : z ≅ t) (cn : z' ≅ t')
    (r : S.obj x ⟶ y) (rp : S.obj p ⟶ p') (rq : S.obj q ⟶ q')
    (redT : et ⟶ t') (ap : ea ⟶ a') (aq : eb ⟶ b')
    (cs : zE ⟶ ez) (d : ez ⟶ et) (aMap : zE ⟶ z')
    (hm : k.hom ≫ T.map (Prod.mkHom fp.inv fq.inv) ≫ vm.inv ≫ uModel.hom = cm.hom)
    (hn : j.hom ≫ T'.map (Prod.mkHom gp.inv gq.inv) ≫ vn.inv ≫ vModel.hom = cn.hom)
    (hs : kE.hom ≫ T'.map (Prod.mkHom ep.inv eq.inv) ≫ μ.inv.app (a, b) ≫
      S.map k.inv ≫ eZ.hom = cs)
    (hr : r ≫ vModel.hom = S.map uModel.hom ≫ eT.hom ≫ redT)
    (hp : rp ≫ gp.hom = S.map fp.hom ≫ ep.hom ≫ ap)
    (hq : rq ≫ gq.hom = S.map fq.hom ≫ eq.hom ≫ aq)
    (he : S.map cm.hom ≫ eT.hom = eZ.hom ≫ d)
    (ha : kE.hom ≫ T'.map (Prod.mkHom ap aq) = aMap ≫ j.hom)
    (hc : cs ≫ d ≫ redT = aMap ≫ cn.hom) :
    r ≫ vn.hom = S.map vm.hom ≫ μ.hom.app (p, q) ≫ T'.map (Prod.mkHom rp rq) := by
  let W : zE ≅ S.obj x := kE ≪≫ T'.mapIso (ep.symm.prod eq.symm) ≪≫
    μ.symm.app (a, b) ≪≫ S.mapIso (T.mapIso (fp.symm.prod fq.symm)) ≪≫
      S.mapIso vm.symm
  let Z : T'.obj (p', q') ≅ t' := T'.mapIso (gp.prod gq) ≪≫ j.symm ≪≫ cn
  have hn' : vn.hom ≫ Z.hom = vModel.hom := by
    simp only [Z, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom]
    rw [← hn]
    simp only [Iso.inv_hom_id_assoc]
    rw [← T'.map_comp_assoc]
    have hg : Prod.mkHom gp.hom gq.hom ≫ Prod.mkHom gp.inv gq.inv = 𝟙 _ := by
      ext <;> simp
    rw [hg, T'.map_id]
    simp only [Category.id_comp, Iso.hom_inv_id_assoc]
  have hm' : T.map (Prod.mkHom fp.inv fq.inv) ≫ vm.inv ≫ uModel.hom = k.inv ≫ cm.hom := by
    rw [← hm]
    simp only [Iso.inv_hom_id_assoc]
  have hp' : ep.inv ≫ S.map fp.inv ≫ rp ≫ gp.hom = ap := by
    rw [hp]
    rw [← S.map_comp_assoc, Iso.inv_hom_id, S.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  have hq' : eq.inv ≫ S.map fq.inv ≫ rq ≫ gq.hom = aq := by
    rw [hq]
    rw [← S.map_comp_assoc, Iso.inv_hom_id, S.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  apply (cancel_epi W.hom).1
  apply (cancel_mono Z.hom).1
  simp only [Category.assoc]
  rw [hn', hr]
  have hleft : W.hom ≫ S.map uModel.hom ≫ eT.hom ≫ redT = cs ≫ d ≫ redT := by
    simp only [W, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom,
      Iso.app_hom, Category.assoc]
    rw [← S.map_comp_assoc, ← S.map_comp_assoc, Category.assoc, hm', S.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% he, ← reassoc_of% hs]
  rw [hleft, hc]
  have hnμ := μ.hom.naturality (Prod.mkHom fp.inv fq.inv)
  change S.map (T.map (Prod.mkHom fp.inv fq.inv)) ≫ μ.hom.app (p, q) =
    μ.hom.app (a, b) ≫ T'.map (Prod.mkHom (S.map fp.inv) (S.map fq.inv)) at hnμ
  simp only [W, Z, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom,
    Iso.app_hom, Category.assoc]
  have hvS : S.map vm.inv ≫ S.map vm.hom = 𝟙 _ := by
    rw [← S.map_comp, Iso.inv_hom_id, S.map_id]
  rw [reassoc_of% hvS]
  rw [reassoc_of% hnμ, Iso.inv_hom_id_app_assoc]
  simp only [← T'.map_comp_assoc, prod_comp, hp', hq']
  rw [reassoc_of% ha]
  simp only [Iso.hom_inv_id_assoc]

end TensorDiagram

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

attribute [local irreducible] hasDerived
attribute [local irreducible] SheafOfModules.monoidalCategory
section ReductionProof
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem reduction_naturality (A : Data.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) {P Q : DS.{c, v, max c v r} J B τ} (f : P ⟶ Q) :
    (A.scalar h).T.map ((e.{c, v, max c v r} J B τ m).map f) ≫ reduction J B τ h (A.scalar h) Q =
      reduction J B τ h (A.scalar h) P ≫ (e J B τ n).map f := by
  apply ((A.scalar h).adjunction.homEquiv _ _).injective
  rw [(A.scalar h).adjunction.homEquiv_naturality_left,
    (A.scalar h).adjunction.homEquiv_naturality_right]
  simp only [reduction, Equiv.apply_symm_apply]
  exact (derivedTransition J B τ h).naturality f

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem reduction_on_kflat_evaluation (A : Data.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := B m)
      (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P)) :
    reduction.{c, v, max c v r} J B τ h (A.scalar h) (DerivedCategory.Q.obj P) ≫
        (Functor.mapDerivedCategoryFactors (evaluation.{c, v, max c v r} J B τ n)).hom.app P =
      (A.scalar h).T.map
          ((Functor.mapDerivedCategoryFactors (evaluation.{c, v, max c v r} J B τ m)).hom.app P) ≫
        (A.scalar h).model.ε.app
          (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((((A.scalar h).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
            ((NatTrans.mapHomologicalComplex
              (transition.{c, v, max c v r} J B τ h) (.up ℤ)).app P ≫
              (Functor.mapHomologicalComplexCompIso
                (Iso.refl (evaluation.{c, v, max c v r} J B τ n ⋙
                  res (coefficientMap J B τ h))) (.up ℤ)).inv.app P)) := by
  apply ((A.scalar h).adjunction.homEquiv _ _).injective
  rw [(A.scalar h).adjunction.homEquiv_naturality_right]
  simp only [reduction, Equiv.apply_symm_apply]
  rw [(A.scalar h).adjunction.homEquiv_naturality_left]
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
  have ht := (A.scalar h).transpose_model Pm Pn hP
    ((((A.scalar h).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm δ)
  simp only [Equiv.apply_symm_apply] at ht
  dsimp only [Functor.comp_obj]
  conv_rhs => rw [ht]
  simpa only [derivedTransition, NatTrans.comp_app, Category.assoc, δ] using
    localized_transition_fac
      (evaluation.{c, v, max c v r} J B τ m)
      (evaluation.{c, v, max c v r} J B τ n)
      (res.{c, v, max c v r} (coefficientMap J B τ h))
      (transition.{c, v, max c v r} J B τ h) P

end ReductionProof
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem tensorModelIso_naturality (R : Sheaf J CommRingCat.{max c v r})
    (A : Closed.{c, v, r} J R) (T : Models.{c, v, r} J R A)
    (P P' Q Q' : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P')
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((totalTensor.{c, v, r} J R).map (Prod.mkHom f g)) ≫
      (tensorModelIso.{c, v, r} J R A T P' Q' hP' hQ').hom =
    (tensorModelIso.{c, v, r} J R A T P Q hP hQ).hom ≫
      A.tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) := by
  let ρ : ObjectProperty (CochainComplex (Mod.{c, v, max c v r} J R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
  let f' : (⟨P, hP⟩ : ρ.FullSubcategory) ⟶ ⟨P', hP'⟩ := ObjectProperty.homMk f
  let g' : (⟨Q, hQ⟩ : ρ.FullSubcategory) ⟶ ⟨Q', hQ'⟩ := ObjectProperty.homMk g
  exact T.comparison.hom.naturality (Prod.mkHom f' g')
set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem totalTensor_flatTerms (R : Sheaf J CommRingCat.{max c v r})
    (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
    (flatP : flatTerms.{c, v, r} J R P) (flatQ : flatTerms.{c, v, r} J R Q) :
    flatTerms.{c, v, r} J R ((totalTensor.{c, v, r} J R).obj (P,Q)) := by
  exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model R P Q
    hP hQ flatP flatQ).2.1

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem tensor_reduction_on_representatives (A : Data.{c, v, r} J B τ)
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
    reduction.{c, v, max c v r} J B τ h (A.scalar h)
        (A.closed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (A.tensorEvaluation n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    (A.scalar h).T.map ((A.tensorEvaluation m).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (A.scalarTensor h).hom.app
        ((e.{c, v, max c v r} J B τ m).obj (DerivedCategory.Q.obj P),
          (e.{c, v, max c v r} J B τ m).obj (DerivedCategory.Q.obj Q)) ≫
      (A.levelClosed n).tensor.map
        (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (A.scalar h)
          (DerivedCategory.Q.obj P))
          (reduction.{c, v, max c v r} J B τ h (A.scalar h) (DerivedCategory.Q.obj Q))) := by
  let F := evaluation.{c, v, max c v r} J B τ m
  let G := evaluation.{c, v, max c v r} J B τ n
  let Pm := (F.mapHomologicalComplex (.up ℤ)).obj P
  let Qm := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let Pn := (G.mapHomologicalComplex (.up ℤ)).obj P
  let Qn := (G.mapHomologicalComplex (.up ℤ)).obj Q
  let E := (A.scalar h).model.E
  let EH := E.mapHomologicalComplex (.up ℤ)
  let Tot := (totalTensor.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ)).obj (P, Q)
  let Totm := (totalTensor.{c, v, r} J (B m)).obj (Pm, Qm)
  have hPm := (A.tensorEvaluationModel m).kflat P hP flatP
  have hQm := (A.tensorEvaluationModel m).kflat Q hQ flatQ
  have hPn := (A.tensorEvaluationModel n).kflat P hP flatP
  have hQn := (A.tensorEvaluationModel n).kflat Q hQ flatQ
  have hEP := (A.scalarTensorModel h).kflat Pm hPm flatPm
  have hEQ := (A.scalarTensorModel h).kflat Qm hQm flatQm
  have hTot := coefficientTotalTensor_isKFlat.{r, c, v}
    (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) P Q hP hQ
  have flatTot := totalTensor_flatTerms.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) P Q hP hQ flatP flatQ
  have hFmTot := (A.tensorEvaluationModel m).kflat Tot hTot flatTot
  have hTotm := coefficientTotalTensor_isKFlat.{r, c, v} J (B m) Pm Qm hPm hQm
  let i := tensorModelIso.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) A.closed A.tensorModels P Q hP hQ
  let km := tensorModelIso.{c, v, r} J (B m) (A.levelClosed m) (A.levelTensorModels m)
    Pm Qm hPm hQm
  let kn := tensorModelIso.{c, v, r} J (B n) (A.levelClosed n) (A.levelTensorModels n)
    Pn Qn hPn hQn
  let kE := tensorModelIso.{c, v, r} J (B n) (A.levelClosed n) (A.levelTensorModels n)
    (EH.obj Pm) (EH.obj Qm) hEP hEQ
  let ep := scalarEpsilonIso.{c, v, r} (coefficientMap J B τ h) (A.scalar h) Pm hPm
  let eq := scalarEpsilonIso.{c, v, r} (coefficientMap J B τ h) (A.scalar h) Qm hQm
  let eT := scalarEpsilonIso.{c, v, r} (coefficientMap J B τ h) (A.scalar h)
    ((F.mapHomologicalComplex (.up ℤ)).obj Tot) hFmTot
  let eZ := scalarEpsilonIso.{c, v, r} (coefficientMap J B τ h) (A.scalar h) Totm hTotm
  let fp := F.mapDerivedCategoryFactors.app P
  let fq := F.mapDerivedCategoryFactors.app Q
  let gp := G.mapDerivedCategoryFactors.app P
  let gq := G.mapDerivedCategoryFactors.app Q
  let vm := (A.tensorEvaluation m).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  let vn := (A.tensorEvaluation n).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  let um := (e.{c, v, max c v r} J B τ m).mapIso i.symm ≪≫
    F.mapDerivedCategoryFactors.app Tot
  let un := (e.{c, v, max c v r} J B τ n).mapIso i.symm ≪≫
    G.mapDerivedCategoryFactors.app Tot
  let cm := km ≪≫ (A.levelClosed m).tensor.mapIso (fp.symm.prod fq.symm) ≪≫ vm.symm ≪≫ um
  let cn := kn ≪≫ (A.levelClosed n).tensor.mapIso (gp.symm.prod gq.symm) ≪≫ vn.symm ≪≫ un
  have hcm : cm.hom = DerivedCategory.Q.map ((A.tensorEvaluationModel m).chain P Q) := by
    simpa only [cm, um, F, Pm, Qm, Tot, km, fp, fq, vm, i, e, Iso.trans_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Category.assoc] using
      (A.tensorEvaluationModel m).derived P Q hP hQ flatP flatQ
  have hcn : cn.hom = DerivedCategory.Q.map ((A.tensorEvaluationModel n).chain P Q) := by
    simpa only [cn, un, G, Pn, Qn, Tot, kn, gp, gq, vn, i, e, Iso.trans_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Category.assoc] using
      (A.tensorEvaluationModel n).derived P Q hP hQ flatP flatQ
  refine tensor_reduction_from_model_squares
    (A.scalar h).T (A.levelClosed m).tensor (A.levelClosed n).tensor (A.scalarTensor h)
    vm vn um un km kn kE fp fq gp gq ep eq eT eZ cm cn
    (reduction.{c, v, max c v r} J B τ h (A.scalar h)
      (A.closed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
    (reduction.{c, v, max c v r} J B τ h (A.scalar h) (DerivedCategory.Q.obj P))
    (reduction.{c, v, max c v r} J B τ h (A.scalar h) (DerivedCategory.Q.obj Q))
    (DerivedCategory.Q.map (cochainReduction.{c, v, r} J B τ A h Tot))
    (DerivedCategory.Q.map (cochainReduction.{c, v, r} J B τ A h P))
    (DerivedCategory.Q.map (cochainReduction.{c, v, r} J B τ A h Q))
    (DerivedCategory.Q.map ((A.scalarTensorModel h).chain Pm Qm))
    (DerivedCategory.Q.map (EH.map ((A.tensorEvaluationModel m).chain P Q)))
    (DerivedCategory.Q.map ((totalTensor.{c, v, r} J (B n)).map
      (Prod.mkHom (cochainReduction.{c, v, r} J B τ A h P)
        (cochainReduction.{c, v, r} J B τ A h Q))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [cm, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom]
  · simp only [cn, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom]
  · exact (A.scalarTensorModel h).derived Pm Qm hPm hQm flatPm flatQm hTotm
  · have hn := reduction_naturality.{c, v, r} J B τ A h i.inv
    have ht := reduction_on_kflat_evaluation.{c, v, r} J B τ A h Tot hFmTot
    rw [← cochainReduction_eq_transpose.{c, v, r} J B τ A h Tot] at ht
    have hr₀ := congrArg
      (fun f ↦ f ≫ G.mapDerivedCategoryFactors.hom.app Tot) hn.symm
    simp only [Category.assoc] at hr₀
    have hr₁ := congrArg
      (fun f ↦ (A.scalar h).T.map ((e.{c, v, max c v r} J B τ m).map i.inv) ≫ f) ht
    simpa only [um, un, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Iso.app_hom, Functor.map_comp, Category.assoc, eT, scalarEpsilonIso, asIso_hom, F, G]
      using hr₀.trans hr₁
  · simpa only [fp, gp, ep, F, G, Pm, scalarEpsilonIso, asIso_hom, Iso.app_hom,
      ← cochainReduction_eq_transpose.{c, v, r} J B τ A h P] using
      reduction_on_kflat_evaluation.{c, v, r} J B τ A h P hPm
  · simpa only [fq, gq, eq, F, G, Qm, scalarEpsilonIso, asIso_hom, Iso.app_hom,
      ← cochainReduction_eq_transpose.{c, v, r} J B τ A h Q] using
      reduction_on_kflat_evaluation.{c, v, r} J B τ A h Q hQm
  · rw [hcm]
    simpa only [eT, eZ, scalarEpsilonIso, asIso_hom, EH, E, F, Totm, Functor.comp_map] using
      (A.scalar h).model.ε.naturality ((A.tensorEvaluationModel m).chain P Q)
  · exact (tensorModelIso_naturality.{c, v, r} J (B n) (A.levelClosed n)
      (A.levelTensorModels n) (EH.obj Pm) Pn (EH.obj Qm) Qn hEP hPn hEQ hQn
      (cochainReduction.{c, v, r} J B τ A h P)
      (cochainReduction.{c, v, r} J B τ A h Q)).symm
  · rw [hcn]
    simpa only [← Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ DerivedCategory.Q.map f) (cochain_tensor_reduction.{c, v, r} J B τ A h P Q)

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem exists_kflat_representative (R : Sheaf J CommRingCat.{max c v r})
    (K : D.{c, v, max c v r} J R) :
    ∃ (P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P ∧
      flatTerms.{c, v, r} J R P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨P, p, hP, flatP, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max c v r, c, v}
      (J := J) (R := R) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso p := hp
  refine ⟨P, hP, ?_, ⟨asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩
  intro k
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X k)).symm (flatP k)

private def reductionNat (A : Data.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m) :
    e.{c, v, max c v r} J B τ m ⋙ (A.scalar h).T ⟶ e.{c, v, max c v r} J B τ n where
  app P := reduction.{c, v, max c v r} J B τ h (A.scalar h) P
  naturality _ _ f := reduction_naturality.{c, v, r} J B τ A h f

private def tensorReductionLeft (A : Data.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m) :
    A.closed.tensor ⋙ e.{c, v, max c v r} J B τ m ⋙ (A.scalar h).T ⟶
      (e.{c, v, max c v r} J B τ n).prod (e.{c, v, max c v r} J B τ n) ⋙
        (A.levelClosed n).tensor :=
  Functor.whiskerLeft A.closed.tensor (reductionNat.{c, v, r} J B τ A h) ≫
    (A.tensorEvaluation n).hom

private def tensorReductionRight (A : Data.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m) :
    A.closed.tensor ⋙ e.{c, v, max c v r} J B τ m ⋙ (A.scalar h).T ⟶
      (e.{c, v, max c v r} J B τ n).prod (e.{c, v, max c v r} J B τ n) ⋙
        (A.levelClosed n).tensor :=
  Functor.whiskerRight (A.tensorEvaluation m).hom (A.scalar h).T ≫
    Functor.whiskerLeft ((e.{c, v, max c v r} J B τ m).prod
      (e.{c, v, max c v r} J B τ m)) (A.scalarTensor h).hom ≫
    Functor.whiskerRight ((reductionNat.{c, v, r} J B τ A h).prod
      (reductionNat.{c, v, r} J B τ A h)) (A.levelClosed n).tensor

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
/-- Actual tensor reduction is the tensor of the two reduction adjoints under
canonical evaluation and scalar-extension comparisons. No normalization is assumed.
Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 06YS, applied to the
horizontal transitions in Zheng, Construction 4.1
(blueprint: lem-pur-system-tensor-reduction-formula).
Proof: resolve both system complexes by K-flat complexes with flat terms on the
coefficient sequence site. Evaluation preserves their K-flat class by
`tensorEvaluationModel.kflat`. It preserves flat terms as well: apply the local
finite-relation criterion on the sequence site, and pull the resulting covering sieve
and factorization witnesses back along the vertical inclusion at the chosen level.
The total tensor of two K-flat complexes is K-flat.
For each ordinary module pair, transpose the horizontal restriction by the ordinary
scalar adjunction. Its unit sends a section x to the scalar-extension section of x,
as fixed by `ScalarData.unit_section`. The horizontal restriction of a pure tensor
x tensor y is the tensor of the two restricted sections. Evaluation's ordinary
comparison is the identity on these pure sections, by
`tensorEvaluationModel_ordinary` and `ordinaryEvaluationTensor_existsUnique`.
The scalar comparison has the same pure-section normalization, by
`scalarTensorModel.ordinary_pure`. The sheafification adjunction and generation of
module tensors by pure tensors therefore identify the two ordinary adjoints.
Apply this equality on each (p,q) summand of the total tensor. The `summand` fields
of the two comparison models give equality of chain maps, including the signed
differentials. Localize that chain equality. Use `ScalarData.transpose_model` to
identify the localized ordinary adjoints with the actual reductions. The two
`derived` comparison squares identify the remaining maps with `tensorEvaluation`
and `scalarTensor`. Cancel their invertible representative comparisons; naturality
of the K-flat tensor models gives the displayed equality on representatives.
Finally every derived object admits such a representative, and naturality of the
adjunction transpose transports the equality along the representative isomorphisms.
This proves the formula for arbitrary unbounded systems and arbitrary coefficient
homomorphisms, including the identity index and non-flat quotient maps. -/
theorem tensor_reduction_formula (A : Data.{c, v, r} J B τ)
    (P Q : DS.{c, v, max c v r} J B τ) :
    ∀ {m n : ℕ} (h : n ≤ m),
      reduction.{c, v, max c v r} J B τ h (A.scalar h) (A.closed.tensor.obj (P, Q)) ≫
          (A.tensorEvaluation n).hom.app (P, Q) =
        (A.scalar h).T.map ((A.tensorEvaluation m).hom.app (P, Q)) ≫
          (A.scalarTensor h).hom.app
            ((e.{c, v, max c v r} J B τ m).obj P, (e.{c, v, max c v r} J B τ m).obj Q) ≫
          (A.levelClosed n).tensor.map
            (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (A.scalar h) P)
              (reduction.{c, v, max c v r} J B τ h (A.scalar h) Q)) := by
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
  let L := tensorReductionLeft.{c, v, r} J B τ A h
  let R := tensorReductionRight.{c, v, r} J B τ A h
  have hrep : L.app (DerivedCategory.Q.obj P', DerivedCategory.Q.obj Q') =
      R.app (DerivedCategory.Q.obj P', DerivedCategory.Q.obj Q') :=
    tensor_reduction_on_representatives.{c, v, r} J B τ A h P' Q' hP hQ
      flatP flatQ flatPm flatQm
  change L.app (P, Q) = R.app (P, Q)
  apply (cancel_epi
    ((A.closed.tensor ⋙ e.{c, v, max c v r} J B τ m ⋙ (A.scalar h).T).map
      (iP.prod iQ).hom)).1
  rw [L.naturality, R.naturality, hrep]

end WeilConjectures.SemilinearSections
