/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDescentInterfaces
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcDirectImageCoherentFamily
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcDirectImageFamilyShiftCompatible
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcDirectImageStageExact
import all WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackTriangles
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationShift

/-! # Normalized completed-pullback coefficient families
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
private theorem inverseSquare {C : Type*} [Category C]
    {A B D E F : C} (a : A ≅ B) (b : B ≅ D) (c : D ≅ E)
    (d : A ≅ F) (e : F ≅ E)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom) :
    b.inv ≫ a.inv ≫ d.hom = c.hom ≫ e.inv := by
  apply (cancel_epi (a.hom ≫ b.hom)).mp
  have hh := congrArg (fun z ↦ z ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh.symm

private theorem normalizeInverse {C : Type*} [Category C]
    {A B D E : C} (c : A ≅ B) (b : A ≅ D) (d : D ≅ E) (α : B ≅ E)
    (h : c.inv ≫ b.hom ≫ d.hom = α.hom) :
    d.inv ≫ b.inv ≫ c.hom = α.inv := by
  have he : c.symm ≪≫ b ≪≫ d = α := Iso.ext h
  simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc] using congrArg Iso.inv he

private theorem isoInverseHomHEq {C : Type*} [Category C]
    {A B A' B' : C} (eA : A = B') (eB : B = A')
    (i : A ≅ B) (j : A' ≅ B') (h : HEq i.hom j.inv) : HEq i.inv j.hom := by
  subst B'
  subst A'
  have he : i = j.symm := Iso.ext (eq_of_heq h)
  exact heq_of_eq (congrArg Iso.inv he)

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullScalarCoefficientsInverse
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
    (j : F →ₐ[ℚ_[l]] G) (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l F G j X).map
        ((pbcScalarCompletedPullIso l E F i g).inv.app K) ≫
      (pbcScalarCompletedPullIso l F G j g).inv.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcActualCompletedPull g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j Y).hom.app K) =
    (pbcAmbientScalarComp l E F G i j X).hom.app
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K) ≫
      (pbcScalarCompletedPullIso l E G (j.comp i) g).inv.app K := by
  exact inverseSquare ((pbcScalarCompletedPullIso l F G j g).app
    ((pbcEmbeddingAmbientTensor l E F i Y).obj K))
    ((pbcEmbeddingAmbientTensor l F G j X).mapIso
      ((pbcScalarCompletedPullIso l E F i g).app K))
    ((pbcAmbientScalarComp l E F G i j X).app
      ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K))
    ((pbcActualCompletedPull g (pbcIntegralDatum l G)).mapIso
      ((pbcAmbientScalarComp l E F G i j Y).app K))
    ((pbcScalarCompletedPullIso l E G (j.comp i) g).app K)
    (pbcScalarCompletedPull_coefficients l E F i g G j K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientPullComparison_exists {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
    (f : S ⟶ T) {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    ∃ c : pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω S h ≅
      pbcAmbientScalarExtension l Ω T h ⋙
        pbcActualCompletedPull f (pbcStageDatum.{u} l Ω F), ∀ K, HEq (c.hom.app K)
      ((pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).inv.app K) :=
  StageSystem.conjugateIso_exists
    (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E))
    (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω F))
    (ambientTensor_eq l Ω T h) (ambientTensor_eq l Ω S h)
    (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) f).symm

private def ambientPullComparison {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
    (f : S ⟶ T) {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω S h ≅
      pbcAmbientScalarExtension l Ω T h ⋙
        pbcActualCompletedPull f (pbcStageDatum.{u} l Ω F) :=
  (ambientPullComparison_exists l Ω f h).choose

private theorem ambientPullComparison_heq {V W : Scheme.{u}}
    [IsNoetherian V] [IsNoetherian W] (f : W ⟶ V)
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcAmbientStage l Ω V E) :
    HEq ((ambientPullComparison l Ω f h).hom.app K)
      ((pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).inv.app K) :=
  (ambientPullComparison_exists l Ω f h).choose_spec K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev ambientPullFamily {V W : Scheme.{u}} [IsNoetherian V] [IsNoetherian W]
    (f : W ⟶ V) :
    StageSystem.Morphism (ambientStageSystem l Ω V) (ambientStageSystem l Ω W) where
  Φ E := pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)
  β h := ambientPullComparison l Ω f h
  coh {E F G} h k K := by
    have hb (M : pbcAmbientStage l Ω V E) :
        HEq ((ambientPullComparison l Ω f (h.trans k)).hom.app M)
          ((pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω G)
            ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h))
            f).inv.app M) := by
      rw [finiteInclusion_comp l Ω h k]
      exact ambientPullComparison_heq l Ω f (h.trans k) M
    exact StageSystem.coherence_of_heq
      (A₀ := pbcAmbientStage l Ω V E) (A₁ := pbcAmbientStage l Ω V F)
      (A₂ := pbcAmbientStage l Ω V G) (B₀ := pbcAmbientStage l Ω W E)
      (B₁ := pbcAmbientStage l Ω W F) (B₂ := pbcAmbientStage l Ω W G)
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E))
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω F))
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω G))
      (ambientTensor_eq l Ω V h) (ambientTensor_eq l Ω V k)
      (ambientTensor_comp_eq l Ω V h k)
      (ambientTensor_eq l Ω W h) (ambientTensor_eq l Ω W k)
      (ambientTensor_comp_eq l Ω W h k)
      (ambientPullComparison l Ω f h) (ambientPullComparison l Ω f k)
      (ambientPullComparison l Ω f (h.trans k))
      (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).symm
      (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω F)
        (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω k) f).symm
      (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω G)
        ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) f).symm
      (pbcAmbientScalarAssociator l Ω V h k)
      (pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h)
        (pbcFiniteFieldInclusion l Ω k) V)
      (pbcAmbientScalarAssociator l Ω W h k)
      (pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h)
        (pbcFiniteFieldInclusion l Ω k) W)
      (ambientPullComparison_heq l Ω f h) (ambientPullComparison_heq l Ω f k) hb
      (ambientAssociator_raw l Ω V h k) (ambientAssociator_raw l Ω W h k)
      (fun M ↦ pullScalarCoefficientsInverse l
        (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) f (pbcFiniteField.{u} l Ω G)
        (pbcFiniteFieldInclusion l Ω k) M) K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientPullComparison_inv_heq {V W : Scheme.{u}}
    [IsNoetherian V] [IsNoetherian W] (f : W ⟶ V)
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcAmbientStage l Ω V E) :
    HEq ((ambientPullComparison l Ω f h).inv.app K)
      ((pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).hom.app K) := by
  apply isoInverseHomHEq _ _ ((ambientPullComparison l Ω f h).app K)
    ((pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).app K)
    (ambientPullComparison_heq l Ω f h K)
  · exact congrArg (fun Z ↦ Z.obj
      ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K))
      (ambientTensor_eq l Ω W h)
  · exact congrArg (fun Z ↦
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω F)).obj (Z.obj K))
      (ambientTensor_eq l Ω V h)

section PullOperationAssembly
variable {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ (n : WithBot ℕ∞))]
  [iS : Fact (∀ t : S, IsUnit (l : S.presheaf.stalk t))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev rationalPullFamily (f : S ⟶ T)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω T E),
      PbcIsBoundedConstructibleComplete S (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj)) :
    StageSystem.Morphism (pbcScalarSystem l Ω T dT.out iT.out)
      (pbcScalarSystem l Ω S dS.out iS.out) := by
  let A := restrictAmbientFamily l Ω (ambientPullFamily l Ω f) pres
  have : ∀ E, (A.Φ E).Additive := fun E ↦
    inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)) (pres E)).Additive)
  have : ∀ E, (A.Φ E).Linear (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) := fun E ↦
    inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)) (pres E)).Linear
        (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)))
  exact rationalizeIntegralFamily l Ω A

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalPullFamily_phi (f : S ⟶ T)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω T E),
      PbcIsBoundedConstructibleComplete S (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    (rationalPullFamily l Ω f pres).Φ E = pbcDescentPullback l Ω f pres E := by
  unfold rationalPullFamily
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalPullFamily_betaSpec (f : S ⟶ T)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω T E),
      PbcIsBoundedConstructibleComplete S (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj)) :
    PbcPullbackBetaSpec l Ω f pres (rationalPullFamily l Ω f pres) := by
  unfold rationalPullFamily
  intro E F h eE eF K
  let A := restrictAmbientFamily l Ω (ambientPullFamily l Ω f) pres
  have : ∀ E, (A.Φ E).Additive := fun E ↦
    inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)) (pres E)).Additive)
  have : ∀ E, (A.Φ E).Linear (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) := fun E ↦
    inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)) (pres E)).Linear
        (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)))
  have hi := StageSystem.refl_conjugate ((rationalizeIntegralFamily l Ω A).β h) eE eF
  have hc := congrArg (fun b ↦
    (pbcDescentPullback l Ω f pres F).map
      ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app K) ≫
      b.inv.app (ScalarLocalization.mk K) ≫
      (pbcScalarIntegralComparison l Ω S dS.out iS.out h).hom.app ((A.Φ E).obj K)) hi
  have hb := normalizeInverse
    ((pbcScalarIntegralComparison l Ω S dS.out iS.out h).app ((A.Φ E).obj K))
    (((rationalizeIntegralFamily l Ω A).β h).app (ScalarLocalization.mk K))
    ((pbcDescentPullback l Ω f pres F).mapIso
      ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).app K))
    ((pbcStageLocalization l Ω S F).mapIso ((A.β h).app K))
    (rationalizeIntegralFamily_beta l Ω A h K)
  have hr := (pbcScalarCompletedPull_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f
    dS.out dT.out iS.out iT.out (pres E) (pres F)).exists.choose_spec
      (ScalarLocalization.mk K)
  apply (heq_of_eq hc).trans
  apply (heq_of_eq hb).trans
  apply HEq.trans ?_ hr.symm
  change HEq ((pbcStageLocalization l Ω S F).map
    (ObjectProperty.homMk
      (X := (A.Φ F).obj ((pbcIntegralScalarExtension l Ω T dT.out iT.out h).obj K))
      (Y := (pbcIntegralScalarExtension l Ω S dS.out iS.out h).obj ((A.Φ E).obj K))
      ((ambientPullComparison l Ω f h).inv.app K.obj))) _
  refine StageSystem.fullMap_heq
    (PbcIsBoundedConstructibleComplete S (pbcStageDatum.{u} l Ω F))
    (pbcStageLocalization l Ω S F) ?_ ?_ _ _
    (ambientPullComparison_inv_heq l Ω f h K.obj)
  · exact congrArg (fun Z ↦
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω F)).obj (Z.obj K.obj))
      (ambientTensor_eq l Ω T h)
  · exact congrArg (fun Z ↦ Z.obj
      ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
      (ambientTensor_eq l Ω S h)

end PullOperationAssembly

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

omit [IsNoetherian X] [IsNoetherian Y] dX iX dY iY in
private theorem completionExact (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (pbcActualCompletion d X).IsTriangulated := by
  let P : ObjectProperty (PbcCompletedDerived X d) := PbcIsIntrinsicallyComplete X d
  have : P.IsTriangulated := complete_tri X d
  let adj := Adjunction.ofIsRightAdjoint P.ι
  let : P.ι.leftAdjoint.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : P.ι.leftAdjoint.IsTriangulated := adj.isTriangulated_leftAdjoint
  let sC : (pbcActualCompletion d X).CommShift ℤ :=
    inferInstanceAs ((P.ι.leftAdjoint ⋙ P.ι).CommShift ℤ)
  have hC : letI := sC; (pbcActualCompletion d X).IsTriangulated :=
    inferInstanceAs ((P.ι.leftAdjoint ⋙ P.ι).IsTriangulated)
  have hsC : sC = pbcActualCompletionShift d X := by
    apply (pbcActualCompletionShift_exists d X).unique
    · exact inferInstanceAs (NatTrans.CommShift adj.unit ℤ)
    · exact (pbcActualCompletionShift_exists d X).exists.choose_spec
  exact hsC ▸ hC

omit [IsNoetherian X] [IsNoetherian Y] dX iX dY iY in
private theorem completedPullExact (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (pbcActualCompletedPull f d).IsTriangulated := by
  have : (pbcActualCompletion d X).IsTriangulated := completionExact X d
  have : (pbcActualDerivedPush f d).IsTriangulated := by
    rw [actualPushShift_eq f d]
    exact Functor.instIsTriangulatedDerivedCategoryRightDerivedFunctor (pbcActualModulePush f d)
  have : (pbcActualDerivedAdjunction f d).CommShift ℤ := scalarActualAdjunction_shift f d
  have : (pbcActualDerivedPull f d).IsTriangulated :=
    (pbcActualDerivedAdjunction f d).isTriangulated_leftAdjoint
  change (pbcActualDerivedPull f d ⋙ pbcActualCompletion d X).IsTriangulated
  infer_instance

-- The integral square fixes the rational shift uniquely.
private def pullStageShiftSpec (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω)
    (s : (pbcDescentPullback l Ω f pres E).CommShift ℤ) : Prop := by
  let A := pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)
  let B := pbcConditionalIntegral (pbcStageDatum.{u} l Ω E) A (pres E)
  let eB : B ⋙ pbcStageInclusion l Ω X E ≅ pbcStageInclusion l Ω Y E ⋙ A :=
    Iso.refl _
  let : B.CommShift ℤ := Functor.CommShift.ofComp
    (F := B) (G := pbcStageInclusion l Ω X E) eB ℤ
  let := s
  let e : pbcStageLocalization l Ω Y E ⋙ pbcDescentPullback l Ω f pres E ≅
      B ⋙ pbcStageLocalization l Ω X E := Iso.refl _
  exact (pbcDescentPullback l Ω f pres E).IsTriangulated ∧
    NatTrans.CommShift e.hom ℤ

-- Restrict the canonical exact completed pullback and localize its normalized shift.
private theorem pullStageShift_exists (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! s : (pbcDescentPullback l Ω f pres E).CommShift ℤ,
      pullStageShiftSpec l Ω f pres E s := by
  have hY := cscIntegralTriangulated l (pbcFiniteField.{u} l Ω E) Y
  have hX := cscIntegralTriangulated l (pbcFiniteField.{u} l Ω E) X
  have := hY.1
  have := hY.2
  have := hX.1
  have := hX.2
  let A := pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)
  have : A.IsTriangulated := completedPullExact f (pbcStageDatum.{u} l Ω E)
  let B := pbcConditionalIntegral (pbcStageDatum.{u} l Ω E) A (pres E)
  let eB : B ⋙ pbcStageInclusion l Ω X E ≅ pbcStageInclusion l Ω Y E ⋙ A :=
    Iso.refl _
  let : B.CommShift ℤ := Functor.CommShift.ofComp
    (F := B) (G := pbcStageInclusion l Ω X E) eB ℤ
  have : NatTrans.CommShift eB.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := B)
      (G := pbcStageInclusion l Ω X E) eB ℤ
  have : B.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right eB).2 inferInstance
  let Q := pbcStageLocalization l Ω Y E
  let Q' := pbcStageLocalization l Ω X E
  let W := Rationalization.W (Submonoid.powers (pbcStageUniformizer.{u} l Ω E))
    (pbcIntegralStage l Ω Y E)
  have : Q.IsLocalization W := ScalarLocalization.pbcScalarLocalization_isLocalization
    (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcIntegralStage l Ω Y E) (pbcStageUniformizer.{u} l Ω E)
  have : (pbcDescentPullback l Ω f pres E).Additive :=
    inferInstanceAs ((ScalarLocalization.transport
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
      (pbcStageUniformizer.{u} l Ω E) B).Additive)
  have hQ : ∀ T : Triangle (pbcStageCategory l Ω Y E),
      T ∈ distTriang _ ↔ ∃ T' : Triangle (pbcIntegralStage l Ω Y E),
        T' ∈ distTriang _ ∧ Nonempty (T ≅ Q.mapTriangle.obj T') :=
    (qbarStagePretriangulated_exists l Ω Y E).exists.choose_spec
  have hQ' : ∀ T : Triangle (pbcIntegralStage l Ω X E), T ∈ distTriang _ →
      Q'.mapTriangle.obj T ∈ distTriang _ := by
    intro T hT
    exact ((qbarStagePretriangulated_exists l Ω X E).exists.choose_spec _).2
      ⟨T, hT, ⟨Iso.refl _⟩⟩
  exact localizeExact Q W Q' B
    (pbcDescentPullback l Ω f pres E) (Iso.refl _) hQ hQ'

-- The choice is determined uniquely by the proved localization square.
@[instance_reducible] private def pullStageCommShift (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcDescentPullback l Ω f pres E).CommShift ℤ :=
  (pullStageShift_exists l Ω f pres E).exists.choose

private abbrev integralPull {Y X : Scheme.{u}} (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)) (pres E)

private abbrev integralPullShift {Y X : Scheme.{u}}
    [IsNoetherian Y] [IsNoetherian X] (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) : (integralPull l Ω f pres E).CommShift ℤ := by
  let e : integralPull l Ω f pres E ⋙ pbcStageInclusion l Ω X E ≅
      pbcStageInclusion l Ω Y E ⋙ pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E) :=
    Iso.refl _
  exact Functor.CommShift.ofComp (F := integralPull l Ω f pres E)
    (G := pbcStageInclusion l Ω X E) e ℤ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit dX iX dY iY in
private theorem ambientPullComparisonShift (f : X ⟶ Y)
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    NatTrans.CommShift (ambientPullComparison l Ω f h).hom ℤ := by
  have hs := (pbcScalarOperations_shift l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).2
  have := hs
  have hi : NatTrans.CommShift
      (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).inv ℤ :=
    inferInstance
  exact comparisonShiftOfHEq _ _
    (ambientTensor_eq l Ω Y h) (ambientTensor_eq l Ω X h)
    (ambientScalarShift_heq l Ω Y h) (ambientScalarShift_heq l Ω X h)
    (ambientPullComparison l Ω f h)
    (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).symm
    (ambientPullComparison_heq l Ω f h) hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralPullComparisonShift (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    letI : (integralPull l Ω f pres E).CommShift ℤ := integralPullShift l Ω f pres E
    letI : (integralPull l Ω f pres F).CommShift ℤ := integralPullShift l Ω f pres F
    NatTrans.CommShift
      ((restrictAmbientFamily l Ω (ambientPullFamily l Ω f) pres).β h).hom ℤ := by
  let AE := pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)
  let AF := pbcActualCompletedPull f (pbcStageDatum.{u} l Ω F)
  let BE := integralPull l Ω f pres E
  let BF := integralPull l Ω f pres F
  let : BE.CommShift ℤ := integralPullShift l Ω f pres E
  let : BF.CommShift ℤ := integralPullShift l Ω f pres F
  let U := pbcAmbientScalarExtension l Ω Y h
  let V := pbcAmbientScalarExtension l Ω X h
  let I := pbcIntegralScalarExtension l Ω Y dY.out iY.out h
  let J := pbcIntegralScalarExtension l Ω X dX.out iX.out h
  let bA := ambientPullComparison l Ω f h
  let b := (restrictAmbientFamily l Ω (ambientPullFamily l Ω f) pres).β h
  let eBE : BE ⋙ pbcStageInclusion l Ω X E ≅ pbcStageInclusion l Ω Y E ⋙ AE :=
    Iso.refl _
  let eBF : BF ⋙ pbcStageInclusion l Ω X F ≅ pbcStageInclusion l Ω Y F ⋙ AF :=
    Iso.refl _
  let eI : I ⋙ pbcStageInclusion l Ω Y F ≅ pbcStageInclusion l Ω Y E ⋙ U :=
    Iso.refl _
  let eJ : J ⋙ pbcStageInclusion l Ω X F ≅ pbcStageInclusion l Ω X E ⋙ V :=
    Iso.refl _
  have : NatTrans.CommShift eBE.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := BE)
      (G := pbcStageInclusion l Ω X E) eBE ℤ
  have : NatTrans.CommShift eBF.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := BF)
      (G := pbcStageInclusion l Ω X F) eBF ℤ
  have : NatTrans.CommShift eI.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := I)
      (G := pbcStageInclusion l Ω Y F) eI ℤ
  have : NatTrans.CommShift eJ.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := J)
      (G := pbcStageInclusion l Ω X F) eJ ℤ
  let e3 : (I ⋙ BF) ⋙ pbcStageInclusion l Ω X F ≅
      pbcStageInclusion l Ω Y E ⋙ (U ⋙ AF) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I eBF ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eI AF ≪≫
      Functor.associator _ _ _
  have : NatTrans.CommShift e3.hom ℤ := by
    exact (pbcAssocWhiskerShift eI eBF).1
  have : NatTrans.CommShift bA.hom ℤ := ambientPullComparisonShift l Ω f h
  apply ScalarLocalization.cscAssocShift eBE eJ e3 b.hom bA.hom
  ext K
  simp only [e3, eBE, eBF, eI, eJ, Iso.refl_hom,
    NatTrans.comp_app, NatTrans.id_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.trans_inv,
    Iso.symm_inv, Iso.refl_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [AF.map_id, Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalPullComparisonShift (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    letI : (pbcDescentPullback l Ω f pres E).CommShift ℤ :=
      pullStageCommShift l Ω f pres E
    letI : (pbcDescentPullback l Ω f pres F).CommShift ℤ :=
      pullStageCommShift l Ω f pres F
    NatTrans.CommShift
      (F₁ := pbcDescentPullback l Ω f pres E ⋙ pbcScalarExtension l Ω X dX.out iX.out h)
      (F₂ := pbcScalarExtension l Ω Y dY.out iY.out h ⋙ pbcDescentPullback l Ω f pres F)
      ((rationalPullFamily l Ω f pres).β h).hom ℤ := by
  let A := restrictAmbientFamily l Ω (ambientPullFamily l Ω f) pres
  let BE := integralPull l Ω f pres E
  let BF := integralPull l Ω f pres F
  let : BE.CommShift ℤ := integralPullShift l Ω f pres E
  let : BF.CommShift ℤ := integralPullShift l Ω f pres F
  let RE := pbcDescentPullback l Ω f pres E
  let RF := pbcDescentPullback l Ω f pres F
  let : RE.CommShift ℤ := pullStageCommShift l Ω f pres E
  let : RF.CommShift ℤ := pullStageCommShift l Ω f pres F
  let QYE := pbcStageLocalization l Ω Y E
  let QXE := pbcStageLocalization l Ω X E
  let QYF := pbcStageLocalization l Ω Y F
  let QXF := pbcStageLocalization l Ω X F
  let I := pbcIntegralScalarExtension l Ω Y dY.out iY.out h
  let J := pbcIntegralScalarExtension l Ω X dX.out iX.out h
  let TY := pbcScalarExtension l Ω Y dY.out iY.out h
  let TX := pbcScalarExtension l Ω X dX.out iX.out h
  let bI := A.β h
  let b := (rationalPullFamily l Ω f pres).β h
  have : NatTrans.CommShift bI.hom ℤ := integralPullComparisonShift l Ω f pres h
  let eE : QYE ⋙ RE ≅ BE ⋙ QXE := Iso.refl _
  let eF : QYF ⋙ RF ≅ BF ⋙ QXF := Iso.refl _
  let eY : QYE ⋙ TY ≅ I ⋙ QYF := pbcScalarIntegralComparison l Ω Y dY.out iY.out h
  let eX : QXE ⋙ TX ≅ J ⋙ QXF := pbcScalarIntegralComparison l Ω X dX.out iX.out h
  have : NatTrans.CommShift eE.hom ℤ :=
    (pullStageShift_exists l Ω f pres E).exists.choose_spec.2
  have : NatTrans.CommShift eF.hom ℤ :=
    (pullStageShift_exists l Ω f pres F).exists.choose_spec.2
  have : NatTrans.CommShift eY.hom ℤ :=
    (pbcScalarShift_exists l Ω Y dY.out iY.out h).exists.choose_spec
  have : NatTrans.CommShift eX.hom ℤ :=
    (pbcScalarShift_exists l Ω X dX.out iX.out h).exists.choose_spec
  let e3 : QYE ⋙ (TY ⋙ RF) ≅ (I ⋙ BF) ⋙ QXF :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eY RF ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I eF ≪≫
      (Functor.associator _ _ _).symm
  have : NatTrans.CommShift e3.hom ℤ := by
    simpa only [e3, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Category.assoc] using
      (pbcAssocWhiskerShift eY.symm eF.symm).2
  apply ScalarLocalization.cscAssocShiftOfWhiskerLeft eE eX e3 bI.hom b.hom
  · intro K
    have : ∀ E, (A.Φ E).Additive := fun E ↦
      inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)) (pres E)).Additive)
    have : ∀ E, (A.Φ E).Linear (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) := fun E ↦
      inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)) (pres E)).Linear
          (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)))
    have hn := rationalizeIntegralFamily_beta l Ω A h K
    have hc := unnormalize (eX.app (BE.obj K)) (RF.mapIso (eY.app K))
      (b.hom.app (QYE.obj K)) (QXF.map (bI.hom.app K)) hn
    simp only [eE, e3, eF, Iso.refl_hom, Iso.refl_inv, Iso.trans_inv, Iso.symm_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app, NatTrans.id_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    erw [Category.id_comp]
    exact hc
  · intro K
    exact ⟨K.obj, 𝟙 _, by infer_instance⟩

/-- The actual rationalized completed-pullback operations form a coherent exact family,
with the prescribed normalized scalar comparisons at every pair of stages. -/
theorem pbcPullbackCoherentFamily (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj)) :
    ∃ F : StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out),
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        F.base.Φ E = pbcDescentPullback l Ω f pres E) ∧
      PbcPullbackBetaSpec l Ω f pres F.base := by
  let R := rationalPullFamily l Ω f pres
  let cs : ∀ E : Padic.FiniteCoefficientFields l Ω, (R.Φ E).CommShift ℤ :=
    fun E ↦ pullStageCommShift l Ω f pres E
  let := cs
  refine ⟨{
    base := R
    additive := ?_
    commShift := cs
    betaCommShift := fun {_ _} h ↦ rationalPullComparisonShift l Ω f pres h
    triangulated := fun E ↦ (pullStageShift_exists l Ω f pres E).exists.choose_spec.1 },
    rationalPullFamily_phi l Ω f pres, rationalPullFamily_betaSpec l Ω f pres⟩
  intro E
  exact inferInstanceAs ((ScalarLocalization.transport
    (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcStageUniformizer.{u} l Ω E)
    (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)) (pres E))).Additive)

end AlgebraicGeometry.Scheme
