/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.StrictIntegralRoosTransport
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.SmoothPurity.Completed.CompletedScalarShiftDescent
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.ProperBaseChange.IntegralCompletionMatchingOnGood
import all WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackShifts
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
import all WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackComparison

set_option linter.privateModule false

/-! # Signed shifts of the recoded strict Roos comparison

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-strict-integral-roos-transport-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  WeilConjectures.scalarReductionSourceDerived WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.integralCompletedRingHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

set_option backward.inferInstanceAs.wrap false in
set_option backward.inferInstanceAs.wrap false in
private theorem complexMap_shift
    {C : Type*} [Category C] [Preadditive C]
    {M₀ M₁ K₀ K₁ R₀ R₁ : CochainComplex C ℤ} {r : ℤ}
    (b₀ : M₀ ⟶ R₀) (b₁ : M₁ ⟶ R₁) (a₀ : M₀ ⟶ K₀) (a₁ : M₁ ⟶ K₁)
    (k₀ : ∀ j, K₀.X j ⟶ R₀.X j) (k₁ : ∀ j, K₁.X j ⟶ R₁.X j)
    (m : M₁ ⟶ M₀⟦r⟧) (k : K₁ ⟶ K₀⟦r⟧) (s : R₁ ⟶ R₀⟦r⟧)
    (h₀ : ∀ j, b₀.f j = a₀.f j ≫ k₀ j)
    (h₁ : ∀ j, b₁.f j = a₁.f j ≫ k₁ j)
    (hk : ∀ j, k₁ j ≫ s.f j = k.f j ≫ k₀ (j + r) ≫
      (CochainComplex.shiftFunctorObjXIso R₀ r j (j + r) rfl).inv)
    (hp : m ≫ a₀⟦r⟧' = a₁ ≫ k) : m ≫ b₀⟦r⟧' = b₁ ≫ s := by
  apply HomologicalComplex.hom_ext
  intro j
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
  rw [h₀, h₁]
  simp only [Category.assoc]
  rw [hk j]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]
  have h := congrArg (fun f ↦ f.f j) hp
  simpa only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    Category.assoc] using congrArg (fun f ↦ f ≫ k₀ (j + r)) h

-- Elaborating concrete product and cocone coordinates unfolds large coefficient models.
private def ordinarySquare (i : PbcProperIntegralPullbackIdentification l E g) :
    ordinaryIntegralPullComplex l E g ⋙ pbcIntegralTransportComplex X l E ≅
      pbcIntegralTransportComplex Y l E ⋙
        (completedModulePullback g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso i.moduleIso (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcIntegralTransportModules Y l E ⋙
        completedModulePullback g (pbcIntegralDatum l E))) (.up ℤ)).symm

private theorem commShift_of_eq
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F H : C ⥤ D} [F.CommShift ℤ] [H.CommShift ℤ]
    {t t' : F ⟶ H} [NatTrans.CommShift t' ℤ] (h : t = t') :
    NatTrans.CommShift t ℤ := by
  cases h
  infer_instance

private theorem commShift_of_comp_iso
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F H K : C ⥤ D} [F.CommShift ℤ] [H.CommShift ℤ] [K.CommShift ℤ]
    (t : F ⟶ H) (a : H ⟶ K) (b : F ⟶ K) [IsIso a]
    [NatTrans.CommShift a ℤ] [NatTrans.CommShift b ℤ] (h : t ≫ a = b) :
    NatTrans.CommShift t ℤ := by
  have : NatTrans.CommShift (inv a) ℤ := NatTrans.CommShift.of_isIso a ℤ
  have ht : t = b ≫ inv a := by
    rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact commShift_of_eq ht

private theorem comparison_shift_of_coordinates
    {C D B A : Type*} [Category C] [Category D] [Category B] [Category A]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ] [HasShift A ℤ]
    (G : ObjectProperty C) [G.IsStableUnderShift ℤ]
    (Q : C ⥤ D) (T : C ⥤ B) (R : B ⥤ A) (F : D ⥤ A)
    [Q.CommShift ℤ] [T.CommShift ℤ] [R.CommShift ℤ] [F.CommShift ℤ]
    (e : (G.ι ⋙ Q) ⋙ F ≅ G.ι ⋙ T ⋙ R)
    (h : ∀ (P : G.FullSubcategory) (r : ℤ), ∃ hP : G (P.obj⟦r⟧),
      (F.commShiftIso r).hom.app (Q.obj P.obj) ≫ (e.hom.app P)⟦r⟧' =
        F.map ((Q.commShiftIso r).inv.app P.obj) ≫ e.hom.app ⟨P.obj⟦r⟧, hP⟩ ≫
          R.map ((T.commShiftIso r).hom.app P.obj) ≫
            (R.commShiftIso r).hom.app (T.obj P.obj)) :
    let sh (n : ℤ) := G.lift (G.ι ⋙ shiftFunctor _ n)
      (fun P ↦ G.le_shift n _ P.property)
    let shi (n : ℤ) := G.liftCompιIso (G.ι ⋙ shiftFunctor _ n)
      (fun P ↦ G.le_shift n _ P.property)
    let := G.fullyFaithfulι.hasShift sh shi
    let : G.ι.CommShift ℤ :=
      Functor.CommShift.ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi
    NatTrans.CommShift e.hom ℤ := by
  let sh (n : ℤ) := G.lift (G.ι ⋙ shiftFunctor _ n)
    (fun P ↦ G.le_shift n _ P.property)
  let shi (n : ℤ) := G.liftCompιIso (G.ι ⋙ shiftFunctor _ n)
    (fun P ↦ G.le_shift n _ P.property)
  let := G.fullyFaithfulι.hasShift sh shi
  let : G.ι.CommShift ℤ :=
    Functor.CommShift.ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi
  constructor
  intro r
  ext P
  obtain ⟨hP, hP_eq⟩ := h P r
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app]
  rw [Functor.shiftFunctorIso_ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi r]
  simp only [shi, ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app]
  erw [Q.map_id]
  erw [(T ⋙ R).map_id]
  simp only [Category.id_comp, Functor.comp_obj, ObjectProperty.ι_obj]
  apply (cancel_epi (F.map ((Q.commShiftIso r).inv.app P.obj))).1
  simp only [Functor.comp_obj, Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [F.map_id, Category.id_comp]
  exact hP_eq

-- Several derived localization comparisons share large concrete coefficient presentations.
set_option backward.inferInstanceAs.wrap false in
set_option backward.inferInstanceAs.wrap false in
private theorem transport_heq
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (P P' : C ⥤ D) (Q Q' : C' ⥤ D')
    [sP : P.CommShift ℤ] [sP' : P'.CommShift ℤ]
    [sQ : Q.CommShift ℤ] [sQ' : Q'.CommShift ℤ]
    (F : D ⥤ D') [F.CommShift ℤ] (A S T : C ⥤ C') [A.CommShift ℤ]
    (hP : P = P') (hQ : Q = Q') (hsP : HEq sP sP') (hsQ : HEq sQ sQ')
    (a : A ≅ S) (b : S ≅ T) (z : T ⋙ Q ≅ P ⋙ F)
    (h : NatTrans.CommShift
      (Functor.isoWhiskerRight a Q ≪≫ (Functor.isoWhiskerRight b Q ≪≫ z)).hom ℤ)
    (z' : T ⋙ Q' ≅ P' ⋙ F) (hz : HEq z' z) :
    NatTrans.CommShift
      (Functor.isoWhiskerRight a Q' ≪≫ (Functor.isoWhiskerRight b Q' ≪≫ z')).hom ℤ := by
  subst P'
  subst Q'
  cases eq_of_heq hsP
  cases eq_of_heq hsQ
  cases eq_of_heq hz
  exact h

-- The canonical exact-restriction shift is the same dependent function of the ring iso.
private theorem changedEquivalence_unit
    {C D : Type*} [Category C] [Category D] (H : C ≌ D)
    (F : D ⥤ C) (r : F ⋙ H.functor ≅ 𝟭 D) :
    (H.symm.changeFunctor ((Iso.isoCompInverse (H := H) r ≪≫
      Functor.leftUnitor H.inverse).symm)).unitIso.inv = r.hom := by
  ext K
  simp only [Equivalence.changeFunctor, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Iso.trans_hom, Iso.isoCompInverse,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  change H.functor.map (H.unitIso.hom.app (F.obj K)) ≫
    H.functor.map (H.inverse.map (r.hom.app K)) ≫ H.functor.map (𝟙 _) ≫
      H.counit.app K = r.hom.app K
  erw [H.functor.map_id, Category.id_comp]
  have hn := H.counit.naturality (r.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [hn, ← Category.assoc]
  change (H.functor.map (H.unitIso.hom.app (F.obj K)) ≫
    H.counitIso.hom.app (H.functor.obj (F.obj K))) ≫ r.hom.app K = r.hom.app K
  exact (congrArg (fun f ↦ f ≫ r.hom.app K)
    (H.functor_unitIso_comp (F.obj K))).trans (Category.id_comp _)

private theorem coefficientUnit (W : Scheme.{u}) :
    (purCoefficientModel l E W).unitIso.inv =
      (purDerivedCoefficientRoundTrip l E W).hom :=
  changedEquivalence_unit (integralDetailedTransport W l E).asEquivalence _ _

section
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end

end WeilConjectures.IntegralCompletedComparison
