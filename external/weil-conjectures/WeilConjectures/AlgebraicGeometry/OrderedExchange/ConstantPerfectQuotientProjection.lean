/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
import WeilConjectures.AlgebraicGeometry.OrderedExchange.ConstantQuotientTensorComparison
import WeilConjectures.AlgebraicGeometry.SignedProjectionResolution.SignedProjectionResolutionNormalization

/-! # Perfect projection for one constant quotient

## References

* Stacks 0941
* Stacks 0B56, 099M
* Stacks 0944, reduction from finite-projective to finite-free coefficients
* Stacks 06YY and the strict-perfect coefficient step of Stacks 0944
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

/-- Exact derived evaluation of a strict quotient diagram. -/
abbrev quotientEvaluation (T : Scheme.{t}) (n : ℕᵒᵖ) : TD (A := A) T ⥤ D (A := A) T :=
  ((CategoryTheory.evaluation ℕᵒᵖ
    (reductionModules T (exchangeConstantRing T A))).obj n).mapDerivedCategory

/-- The canonical comparison of evaluation and pullback. -/
abbrev quotientEvaluationPull (n : ℕᵒᵖ) :=
  AlgebraicGeometry.ProEtale.StrictTower.evalG A f n.unop

/-- The mate of the inverse pullback/evaluation comparison. -/
abbrev quotientEvaluationPush (n : ℕᵒᵖ) :=
  AlgebraicGeometry.ProEtale.StrictTower.evalR A f n.unop

/-- The normalized reduction/pullback square at one fixed quotient. -/
def quotientTensorPull (n : ℕᵒᵖ) :
    (reduction d V ⋙ quotientEvaluation (A := A) V n) ⋙ pull (A := A) f ≅
      pull (A := A) f ⋙ (reduction d U ⋙ quotientEvaluation (A := A) U n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (reduction d V)
      (quotientEvaluationPull (A := A) f n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (reductionPullIso d f) (quotientEvaluation U n) ≪≫
          Functor.associator _ _ _

/-- The finite projection is the counit mate of the specified normalized square. -/
def quotientProjection (n : ℕᵒᵖ) :
    push (A := A) f ⋙ (reduction d V ⋙ quotientEvaluation V n) ⟶
      (reduction d U ⋙ quotientEvaluation U n) ⋙ push (A := A) f :=
  mateEquiv
    (proEtaleRingDerivedAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (proEtaleRingDerivedAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A)) (quotientTensorPull d f n).hom

/-- A perfect quotient has an actual bounded finite-projective augmentation.
The K-projective lifting lemma realizes the given derived isomorphism. -/
private theorem scalarResolution (n : ℕ) :
    ∃ (F : CochainComplex (ModuleCat.{t + 1} A) ℤ) (a b : ℤ)
      (q : F ⟶ (CochainComplex.singleFunctor _ 0).obj
        (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))),
      QuasiIso q ∧
      (∀ i : ℤ, Module.Projective A (F.X i) ∧ Module.Finite A (F.X i)) ∧
      (∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i)) := by
  let := HasDerivedCategory.standard (ModuleCat.{t + 1} A)
  obtain ⟨F, a, b, ha, hb, hF, ⟨eF⟩⟩ :=
    d.quotientPerfect (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have := ha
  have := hb
  have (i : ℤ) : Module.Projective A (F.X i) := (hF i).1
  have (i : ℤ) : Projective (F.X i) := inferInstance
  let Q := (CochainComplex.singleFunctor (ModuleCat.{t + 1} A) 0).obj
    (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))
  obtain ⟨q, hq⟩ := DerivedCategory.Q_map_surjective_of_projective F Q b eF.inv
  have : IsIso (DerivedCategory.Q.map q) := by rw [hq]; infer_instance
  refine ⟨F, a, b, q,
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{t + 1} A) q).mp inferInstance,
    hF, ?_⟩
  intro i hi
  rcases hi with hi | hi
  · exact F.isZero_of_isStrictlyGE a i hi
  · exact F.isZero_of_isStrictlyLE b i hi

private def scalarRestrictionIdentity (T : Scheme.{t}) :
    reductionRestrict T (𝟙 (exchangeConstantRing T A)) ≅
      𝟭 (reductionModules T (exchangeConstantRing T A)) :=
  NatIso.ofComponents (fun M ↦ Iso.refl M) (fun _ ↦ rfl)

private def constantUnit (T : Scheme.{t}) :
    (adicLisseConstantModules T A).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit ((adicLisseForget T).obj (exchangeConstantRing T A)) := by
  let φ := 𝟙 (exchangeConstantRing T A)
  let a := (pbcScalarAdjunction φ).ofNatIsoRight (scalarRestrictionIdentity T)
  let e : completedAdicChange T φ ≅ 𝟭 _ := a.leftAdjointUniq Adjunction.id
  exact (e.app _).symm ≪≫ CompletedConstantReduction.constantChange_unit T φ

/-- Exact constant realization preserves the chosen finite-free splitting. -/
private theorem constantFiniteRetract (T : Scheme.{t})
    (N : ModuleCat.{t + 1} A) [Module.Finite A N] [Module.Projective A N] :
    ∃ r : ℕ,
      ∃ i : (adicLisseConstantModules T A).obj N ⟶
        ∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
          ((adicLisseForget T).obj (exchangeConstantRing T A)),
      ∃ p : (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
          ((adicLisseForget T).obj (exchangeConstantRing T A))) ⟶
        (adicLisseConstantModules T A).obj N,
      i ≫ p = 𝟙 _ := by
  let G := adicLisseConstantModules T A
  have : HasFiniteBiproducts (reductionModules T (exchangeConstantRing T A)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : G.Additive := CompletedConstantReduction.constant_additive T A
  have : PreservesFiniteColimits G := (CompletedConstantReduction.constant_exact T A).2
  obtain ⟨r, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A N
  let V := fun _ : Fin r ↦ ModuleCat.of A A
  let j : ModuleCat.of A (Fin r → A) ≅ ∐ V :=
    (ModuleCat.piIsoPi V).symm ≪≫ biproductIso V
  let e : G.obj (∐ V) ≅ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
      ((adicLisseForget T).obj (exchangeConstantRing T A))) :=
    PreservesCoproduct.iso G V ≪≫ Sigma.mapIso (fun _ ↦ constantUnit T) ≪≫
      (biproductIso _).symm
  refine ⟨r, G.map (ModuleCat.ofHom g ≫ j.hom) ≫ e.hom,
    e.inv ≫ G.map (j.inv ≫ ModuleCat.ofHom f), ?_⟩
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h : ModuleCat.ofHom g ≫ ModuleCat.ofHom f = 𝟙 N := ModuleCat.hom_ext hfg
  rw [h, G.map_id]

/-- Realize the scalar resolution on the original site, including its actual augmentation,
finite-free retractions, finite support, and the flat K-flat property. -/
private theorem constantResolution (T : Scheme.{t}) (n : ℕ) :
    ∃ (F : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ)
      (a b : ℤ)
      (q : F ⟶ (CochainComplex.singleFunctor _ 0).obj
        ((adicLisseConstantModules T A).obj
          (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1))))),
      QuasiIso q ∧
      Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite
        ((adicLisseForget T).obj (exchangeConstantRing T A)) F) ∧
      (∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i)) ∧
      proEtaleFlatRepresentatives T (exchangeConstantRing T A) F := by
  classical
  obtain ⟨F, a, b, q, hq, hF, hb⟩ := scalarResolution d n
  have : (adicLisseConstantModules T A).Additive :=
    CompletedConstantReduction.constant_additive T A
  have : PreservesFiniteLimits (adicLisseConstantModules T A) :=
    (CompletedConstantReduction.constant_exact T A).1
  have : PreservesFiniteColimits (adicLisseConstantModules T A) :=
    (CompletedConstantReduction.constant_exact T A).2
  let C := (CompletedConstantReduction.constantComplex T A).obj F
  have hret (i : ℤ) := @constantFiniteRetract _ _ T (F.X i) (hF i).2 (hF i).1
  choose N v w hvw using hret
  let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (exchangeConstantRing T A)) C :=
    { N := N
      i := v
      p := w
      splitting := hvw }
  have hb' (i : ℤ) (hi : i < a ∨ b < i) : IsZero (C.X i) :=
    (adicLisseConstantModules T A).map_isZero (hb i hi)
  refine ⟨C, a, b, CompletedConstantReduction.constantAugmentation T d.ideal n F q,
    ?_, ⟨pkg⟩, hb', ?_⟩
  · have := hq
    unfold CompletedConstantReduction.constantAugmentation
      CompletedConstantReduction.constantComplex
    infer_instance
  · exact proEtaleStrictPerfect_flat _ C pkg ⟨a, b, hb'⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projection_transport
    {C E : Type*} [Category C] [Category E]
    (L : C ⥤ E) (R : E ⥤ C) (adj : L ⊣ R)
    (T : C × C ⥤ C) (S : E × E ⥤ E)
    (mu : T ⋙ L ≅ (L.prod L) ⋙ S) (Q : C)
    (H : C ⥤ C) (J : E ⥤ E) (theta : H ⋙ L ≅ L ⋙ J)
    (eH : H ≅ (Functor.curryObj T).flip.obj Q)
    (eJ : J ≅ (Functor.curryObj S).flip.obj (L.obj Q))
    (hs : ∀ M : C, L.map (eH.hom.app M) ≫ mu.hom.app (M, Q) =
      theta.hom.app M ≫ eJ.hom.app (L.obj M)) (K : E) :
    eH.hom.app (R.obj K) ≫ derivedProjectionFormulaMate L R adj T S mu K Q =
      (mateEquiv adj adj theta.hom).app K ≫ R.map (eJ.hom.app K) := by
  have hc : L.map (derivedProjectionFormulaMate L R adj T S mu K Q) ≫
      adj.counit.app (S.obj (K, L.obj Q)) = mu.hom.app (R.obj K, Q) ≫
        S.map (Prod.mkHom (adj.counit.app K) (𝟙 (L.obj Q))) := by
    have h := adj.map_rightAdjointProjectionMap_app_app_comp_counit
      (T_C := Functor.curry.obj S) (T_D := Functor.curry.obj T)
      (Functor.curry.map mu.hom ≫ (Functor.curryObjProdComp L L S).hom) K Q
    change L.map (derivedProjectionFormulaMate L R adj T S mu K Q) ≫
      adj.counit.app (S.obj (K, L.obj Q)) =
      (mu.hom.app (R.obj K, Q) ≫ 𝟙 _) ≫
        S.map (Prod.mkHom (adj.counit.app K) (𝟙 (L.obj Q))) at h
    simpa only [Category.comp_id] using h
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hc, adj.counit_naturality]
  rw [← Category.assoc (L.map ((mateEquiv adj adj theta.hom).app K)),
    mateEquiv_counit adj adj theta.hom K, Category.assoc]
  rw [← Category.assoc, hs, Category.assoc]
  exact congrArg (fun z ↦ theta.hom.app (R.obj K) ≫ z)
    (eJ.hom.naturality (adj.counit.app K)).symm

/-- The finite counit projection is invertible for a perfect quotient. -/
theorem quotientProjection_isIso (n : ℕᵒᵖ) (K : D (A := A) U) :
    IsIso ((quotientProjection d f n).app K) := by
  obtain ⟨F, lo, hi, q, hq, ⟨package⟩, hb, hF⟩ := constantResolution d V n.unop
  obtain ⟨a, b, eV, eU, hs⟩ := constantQuotientTensorComparison d f n.unop F hF q hq
  obtain ⟨I, hI, ⟨alpha⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have hn := SignedProjectionResolution.normalization f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A) a b K
    (DerivedCategory.Q.obj F) I hI alpha F (Iso.refl _) package ⟨lo, hi, hb⟩
  have hp : IsIso (derivedProjectionFormulaMate (pull (A := A) f) (push (A := A) f)
      (proEtaleRingDerivedAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A)) a.tensor b.tensor
      (proEtaleCanonicalTensorComparison f (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso f A) a b) K
      (DerivedCategory.Q.obj F)) :=
    ⟨⟨_, hn.2.1, hn.2.2⟩⟩
  have ht := projection_transport (pull (A := A) f) (push (A := A) f)
    (proEtaleRingDerivedAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A)) a.tensor b.tensor
    (proEtaleCanonicalTensorComparison f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A) a b)
    (DerivedCategory.Q.obj F) (reduction d V ⋙ quotientEvaluation V n)
    (reduction d U ⋙ quotientEvaluation U n) (quotientTensorPull d f n) eV eU
    (fun M ↦ by
      simpa only [quotientTensorPull, Iso.trans_hom, NatTrans.comp_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
        Category.comp_id, Category.assoc] using hs M) K
  have : IsIso ((quotientProjection d f n).app K ≫
      (push (A := A) f).map (eU.hom.app K)) := by
    change IsIso (((mateEquiv _ _ (quotientTensorPull d f n).hom).app K) ≫ _)
    rw [← ht]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((push (A := A) f).map (eU.hom.app K))

end AlgebraicGeometry.Scheme.OrderedExchange
