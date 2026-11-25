/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Towers and the derived completion: derived limits

The derived limit is computed by the Roos fibre, is a derived limit of the derived
evaluations, and is compatible with exact equivalences.
Source: blueprint Assertions 4--5 (blueprint: proposition-proper-base-change-complete-integral).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

namespace CompleteDerivedCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The cochain unit of the derived limit, as a natural transformation.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral). -/
def rlimUnit (T : Scheme.{u}) :
    ExactProductsRoos.ordinary ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ rlim l E T where
  app K := (inverseLimit l E T).rightDerivedFunctorUnitQ K
  naturality _ _ f := (inverseLimit l E T).rightDerivedFunctorUnitQ_naturality f

/-- The derived limit is the Roos fibre of `1 - shift`.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral).
Proof: exact countable products and the K-injective normalization of the derived limit
let `lem-weil-pbc-exact-products-roos-comparison` apply. -/
theorem rlim_roos (T : Scheme.{u}) :
    Nonempty (DerivedCategory.Q ⋙ rlim l E T ≅ ExactProductsRoos.fibre ⋙ DerivedCategory.Q) := by
  obtain ⟨e, -⟩ := ExactProductsRoos.comparisonIso (rlim l E T) (rlimUnit l E T) (by
    intro I hI
    have := hI
    change IsIso ((inverseLimit l E T).rightDerivedFunctorUnitQ I)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance)
  exact ⟨e.symm⟩

/-- Derived limits are invariant under isomorphism of the limit object.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral). -/
theorem isDerivedLimit_of_iso {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] {f : ∀ n, K (n + 1) ⟶ K n} {L L' : C}
    (h : IsDerivedLimit f L) (e : L ≅ L') : IsDerivedLimit f L' := by
  obtain ⟨p, δ, hd⟩ := h
  refine ⟨e.inv ≫ p, δ ≫ e.hom⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ hd _ ?_
  refine Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp
  · simp
  · simp [← Functor.map_comp]

private theorem transition_inv_fac (T : Scheme.{u}) (n : ℕ)
    (J : CochainComplex (Tow l E T) ℤ) :
    (ev l E T (n + 1)).mapDerivedCategoryFactors.inv.app J ≫
        (transition l E T n).app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ _).map (homOfLE (Nat.le_succ n)).op) (.up ℤ)).app J) ≫
        (ev l E T n).mapDerivedCategoryFactors.inv.app J := by
  have hm : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ))
      ((ev l E T (n + 1)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (ev l E T (n + 1)).mapDerivedCategory =
        (ev l E T (n + 1)).mapDerivedCategoryFactors := rfl
  have hn : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ))
      ((ev l E T n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (ev l E T n).mapDerivedCategory =
        (ev l E T n).mapDerivedCategoryFactors := rfl
  apply (cancel_mono ((ev l E T n).mapDerivedCategoryFactors.hom.app J)).mp
  simp [transition, towerDerivedEvaluationTransition, Localization.liftNatTrans_app, hm, hn]

private def limitAsFunctorIsoOrdinary (A : Type*) [Category A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    limit I.asFunctor ≅ (ExactProductsRoos.ordinary (B := A)).obj I :=
  ((HomologicalComplex.functorEquivalenceInverseCompMapHomologicalComplexLim A
    (.up ℤ) ℕᵒᵖ).app I.asFunctor).symm

/-- The derived limit is a derived limit of the derived evaluations.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral).
Proof: represent the tower by a K-injective complex; exact countable products give
derived products and the termwise inverse limit computes the derived limit of its
evaluations, which is the derived limit functor on a K-injective complex. -/
theorem rlim_isDerivedLimit (T : Scheme.{u}) :
    ∃ (_products : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E T))),
      ∀ M : DTow l E T,
        IsDerivedLimit (K := fun n : ℕ ↦ (dev l E T n).obj M)
          (fun n : ℕ ↦ (transition l E T n).app M) ((rlim l E T).obj M) := by
  let A := AdicCompletion.Modules l E T
  have : CountableAB4Star A := CountableAB4Star.of_hasExactLimitsOfShape_nat A
  obtain ⟨hP, -, -, h3⟩ := derivedCategory_countableProducts_and_towerLimit.{0} A
  refine ⟨hP, fun M ↦ ?_⟩
  obtain ⟨I, hI, i, -, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    (DerivedCategory.Q.objPreimage M)
  have := hI
  have : IsIso (DerivedCategory.Q.map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hi
  let eM : DerivedCategory.Q.obj I ≅ M :=
    (asIso (DerivedCategory.Q.map i)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso M
  let comp (n : ℕ) : DerivedCategory.Q.obj (I.asFunctor.obj (op n)) ≅ (dev l E T n).obj M :=
    ((ev l E T n).mapDerivedCategoryFactors.app I).symm ≪≫ (dev l E T n).mapIso eM
  let τ : I.asFunctor ⋙ DerivedCategory.Q ⟶
      Functor.ofOpSequence (X := fun n : ℕ ↦ (dev l E T n).obj M)
        (fun n : ℕ ↦ (transition l E T n).app M) :=
    NatTrans.ofOpSequence (G := Functor.ofOpSequence (X := fun n : ℕ ↦ (dev l E T n).obj M)
        (fun n : ℕ ↦ (transition l E T n).app M)) (fun n ↦ (comp n).hom) (by
      intro n
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      dsimp only [comp, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv]
      rw [Category.assoc, (transition l E T n).naturality eM.hom,
        reassoc_of% transition_inv_fac l E T n I]
      rfl)
  have : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    change IsIso (comp n.unop).hom
    infer_instance
  obtain ⟨c, ⟨hc⟩, hL⟩ := h3 inferInstance I _ _ (asIso τ)
  refine isDerivedLimit_of_iso hL ?_
  have : HasLimit I.asFunctor := ⟨⟨c, hc⟩⟩
  let e₁ : c.pt ≅ limit I.asFunctor := hc.conePointUniqueUpToIso (limit.isLimit _)
  let e₂ : limit I.asFunctor ≅ (ExactProductsRoos.ordinary (B := A)).obj I :=
    limitAsFunctorIsoOrdinary A I
  have hu : IsIso ((inverseLimit l E T).rightDerivedFunctorUnitQ I) := by
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  exact DerivedCategory.Q.mapIso (e₁ ≪≫ e₂) ≪≫
    asIso ((inverseLimit l E T).rightDerivedFunctorUnitQ I) ≪≫ (rlim l E T).mapIso eM

end CompleteDerivedCompletion

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

namespace CompleteDerivedCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The derived limit is compatible with exact equivalences of module categories.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral).
Proof: conjugate the constant comparison of the inverse equivalence under the composite
derived adjunctions; the derived functor of an exact functor is its induced functor. -/
theorem rlim_equivalence {T T' : Scheme.{u}}
    (e : AdicCompletion.Modules l E T ≌ AdicCompletion.Modules l E T')
    [e.functor.Additive] :
    Nonempty (rlim l E T ⋙ e.functor.mapDerivedCategory ≅
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj e.functor).mapDerivedCategory ⋙ rlim l E T') := by
  have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
  let eT : Tow l E T ≌ Tow l E T' := e.congrRight
  have : eT.functor.Additive := inferInstanceAs
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj e.functor).Additive
  have : eT.symm.functor.Additive := inferInstanceAs
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj e.inverse).Additive
  let a₁ : e.inverse.mapDerivedCategory ⊣ e.functor.mapDerivedCategory :=
    (e.symm.toAdjunction.mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
      e.functor.rightDerivedFunctorIsoMapDerivedCategory
  let a₂ : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj e.inverse).mapDerivedCategory ⊣
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj e.functor).mapDerivedCategory :=
    (eT.symm.toAdjunction.mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
      eT.functor.rightDerivedFunctorIsoMapDerivedCategory
  exact ⟨conjugateIsoEquiv (a₁.comp (constantLimitAdjunction l E T))
    ((constantLimitAdjunction l E T').comp a₂) (constantInterchange l E e.inverse).symm⟩

/-- Evaluation at the top level is left adjoint to the constant tower functor.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral). -/
def evaluationZeroConstAdjunction (A : Type*) [Category A] :
    (evaluation ℕᵒᵖ A).obj (op 0) ⊣ Functor.const ℕᵒᵖ :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app := fun T ↦ {
        app := fun n ↦ T.map (homOfLE (Nat.zero_le n.unop)).op
        naturality := by
          intro n m t
          change T.map t ≫ T.map _ = T.map _ ≫ 𝟙 _
          rw [Category.comp_id, ← T.map_comp]
          congr 1 }
      naturality := by
        intro T U t
        ext n
        exact (t.naturality (homOfLE (Nat.zero_le n.unop)).op).symm }
    counit := { app := fun X ↦ 𝟙 X }
    left_triangle := by
      ext T
      dsimp
      simp
    right_triangle := by
      ext X n
      dsimp
      simp }

/-- The unit of the derived constant-limit adjunction is an isomorphism.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral).
Proof: constant towers of K-injective complexes are K-injective, so on a K-injective
complex the derived unit is the ordinary unit, which is invertible because the index
category is connected. -/
theorem constantLimit_unit_isIso (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) :
    IsIso ((constantLimitAdjunction l E T).unit.app M) := by
  let A := AdicCompletion.Modules l E T
  let adj : constant l E T ⊣ inverseLimit l E T := constLimAdj
  have := (evaluationZeroConstAdjunction A).preservesKInjectiveComplexes
  have hU : IsIso adj.unit := inferInstance
  have key (I : CochainComplex A ℤ) [I.IsKInjective] :
      IsIso ((constantLimitAdjunction l E T).unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) := by
    have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso A (.up ℤ)) (constant l E T).mapDerivedCategoryFactorsh.hom
      (inverseLimit l E T).rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj I)
    have e1 : IsIso (DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj I))) := by
      rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
      have : IsIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app I) :=
        HomologicalComplex.Hom.isIso_of_components _
      infer_instance
    have e2 : IsIso ((inverseLimit l E T).rightDerivedFunctorUnit.app
        (((constant l E T).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj I))) := by
      change IsIso ((inverseLimit l E T).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj
          (((constant l E T).mapHomologicalComplex (.up ℤ)).obj I)))
      infer_instance
    have : IsIso (DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj I)) ≫
        (inverseLimit l E T).rightDerivedFunctorUnit.app
          (((constant l E T).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj I))) := inferInstance
    rw [← h] at this
    exact (isIso_comp_right_iff _ _).mp this
  obtain ⟨I, hI, i, -, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    (DerivedCategory.Q.objPreimage M)
  have := hI
  have : IsIso (DerivedCategory.Q.map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hi
  let e : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) :=
    (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫ asIso (DerivedCategory.Q.map i) ≪≫
      ((DerivedCategory.quotientCompQhIso A).app I).symm
  have hn := (constantLimitAdjunction l E T).unit.naturality e.hom
  have := key I
  have : IsIso ((constantLimitAdjunction l E T).unit.app M ≫
      (dconstant l E T ⋙ rlim l E T).map e.hom) := by
    rw [← hn]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp this

end CompleteDerivedCompletion

end AlgebraicGeometry.ProEtale
