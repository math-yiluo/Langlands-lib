/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.PullbackScalar.PullbackScalar
import all WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
import all Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import all Mathlib.Algebra.Homology.Functor
import all WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
import all WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement

/-!
# Completed pullback using the reduction tower

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/lemma-weil-pbc-completed-pullback-reduction.md
(blueprint: definition-completed-inverse-image).

The strict comparison is characterized on both cone summands in every degree and
at every tower level. Its descent is characterized on every complex by localization.
Thus neither choice below selects an unspecified isomorphism of derived objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {T T' : Scheme.{u}} (f : T' ⟶ T)

private def scalarCompare : scalarTower l E T ⋙ pull l E f ⟶
    CondensedRing.upperStar (DerivedNakayama.integerRing l E) f ⋙ scalarTower l E T' where
  app M := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro n
    change (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map
      (((Functor.ofOpSequence (X := fun _ : ℕ ↦ 𝟭 (AdicCompletion.Modules l E T))
        (fun _ ↦ scalar l E T)).map (homOfLE (Nat.le_succ n)).op).app M) ≫ 𝟙 _ =
      𝟙 _ ≫ (((Functor.ofOpSequence (X := fun _ : ℕ ↦ 𝟭 (AdicCompletion.Modules l E T'))
        (fun _ ↦ scalar l E T')).map (homOfLE (Nat.le_succ n)).op).app
          ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj M))
    simp only [Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp]
    exact PullbackScalar.scalarOnModules l E f (uniformizer l E) M)
  naturality _ _ g := by
    apply NatTrans.ext
    funext n
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl
private def scalarCompareIso : scalarTower l E T ⋙ pull l E f ≅
    CondensedRing.upperStar (DerivedNakayama.integerRing l E) f ⋙ scalarTower l E T' := by
  have h : IsIso (scalarCompare l E f) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro M
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro n
    change IsIso (𝟙 _)
    infer_instance
  exact asIso (scalarCompare l E f)
private def sourceCompare := NatIso.mapHomologicalComplex (scalarCompareIso l E f) (.up ℤ)
private def targetCompare := NatIso.mapHomologicalComplex
  (Functor.compConstIso ℕᵒᵖ (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).symm
  (.up ℤ)
private theorem powerCompare (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    ((pull l E f).mapHomologicalComplex (.up ℤ)).map ((complexPowerMap l E T).app M) ≫
      (targetCompare l E f).hom.app M =
    (sourceCompare l E f).hom.app M ≫
      (complexPowerMap l E T').app
        (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
          (.up ℤ)).obj M) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext n
  change (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map
      (End.asHom ((End.of ((scalar l E T).app (M.X i))) ^ (n.unop+1))) ≫ 𝟙 _ =
    𝟙 _ ≫ End.asHom ((End.of ((scalar l E T').app
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj (M.X i)))) ^
        (n.unop+1))
  simp only [Category.comp_id, Category.id_comp]
  have hp := congrArg End.asHom <| map_pow
    ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapEnd (M.X i))
    (End.of ((scalar l E T).app (M.X i))) (n.unop+1)
  change _ = End.asHom ((End.of
    ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map
      ((scalar l E T).app (M.X i)))) ^ (n.unop+1)) at hp
  rw [PullbackScalar.scalarOnModules l E f (uniformizer l E)] at hp
  exact hp
private def coneCompare (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso ((complexPowerMap l E T).app M)
    (pull l E f) ≪≫
    CategoryTheory.coneIso _ _ ((sourceCompare l E f).app M)
      ((targetCompare l E f).app M) (powerCompare l E f M)
private theorem coneCompare_natural
    {M N : CochainComplex (AdicCompletion.Modules l E T) ℤ} (g : M ⟶ N) :
    ((pull l E f).mapHomologicalComplex (.up ℤ)).map ((strictRed l E T).map g) ≫
        (coneCompare l E f N).hom =
      (coneCompare l E f M).hom ≫ (strictRed l E T').map
        (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
          (.up ℤ)).map g) := by
  dsimp only [coneCompare, Iso.trans_hom, strictRed]
  rw [← Category.assoc, ConeNaturality.mapCone_natural]
  simp only [Category.assoc]
  rw [CategoryTheory.coneIso_natural]
  · exact (sourceCompare l E f).hom.naturality g
  · exact (targetCompare l E f).hom.naturality g

private def strictCompare :
    strictRed l E T ⋙ (pull l E f).mapHomologicalComplex (.up ℤ) ≅
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
        (.up ℤ) ⋙ strictRed l E T' :=
  NatIso.ofComponents (coneCompare l E f) (fun g ↦ coneCompare_natural l E f g)

private theorem strictCompare_inl
    (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) (i : ℤ) (n : ℕ) :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map
        (((CochainComplex.mappingCone.inl ((complexPowerMap l E T).app M)).v
          (i+1) i (by omega)).app (op n)) ≫
        (((strictCompare l E f).hom.app M).f i).app (op n) =
      ((CochainComplex.mappingCone.inl ((complexPowerMap l E T').app
        (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
          (.up ℤ)).obj M))).v (i+1) i (by omega)).app (op n) := by
  have h : (pull l E f).map
      ((CochainComplex.mappingCone.inl ((complexPowerMap l E T).app M)).v
        (i+1) i (by omega)) ≫ ((strictCompare l E f).hom.app M).f i =
      ((sourceCompare l E f).hom.app M).f (i+1) ≫
        (CochainComplex.mappingCone.inl ((complexPowerMap l E T').app
          (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
            (.up ℤ)).obj M))).v (i+1) i (by omega) := by
    change _ ≫ (_ ≫ _) = _
    rw [← Category.assoc, ConeNaturality.mapCone_inl]
    simp only [CategoryTheory.coneIso, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, Iso.app_hom]
  have hn := congr_app h (op n)
  simp only [NatTrans.comp_app] at hn
  change _ ≫ _ = 𝟙 _ ≫ _ at hn
  simpa only [pull, Functor.whiskeringRight, Functor.whiskerRight,
    Category.id_comp] using hn

private theorem strictCompare_inr
    (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) (i : ℤ) (n : ℕ) :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map
        (((CochainComplex.mappingCone.inr ((complexPowerMap l E T).app M)).f i).app (op n)) ≫
        (((strictCompare l E f).hom.app M).f i).app (op n) =
      ((CochainComplex.mappingCone.inr ((complexPowerMap l E T').app
        (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
          (.up ℤ)).obj M))).f i).app (op n) := by
  have h : (pull l E f).map
      ((CochainComplex.mappingCone.inr ((complexPowerMap l E T).app M)).f i) ≫
        ((strictCompare l E f).hom.app M).f i =
      ((targetCompare l E f).hom.app M).f i ≫
        (CochainComplex.mappingCone.inr ((complexPowerMap l E T').app
          (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
            (.up ℤ)).obj M))).f i := by
    change _ ≫ (_ ≫ _) = _
    have h := congrArg (fun g ↦ g.f i)
      (CochainComplex.mappingCone.map_inr ((complexPowerMap l E T).app M) (pull l E f))
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at h
    rw [← Category.assoc, h]
    simp only [CategoryTheory.coneIso, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f, HomologicalComplex.comp_f, Iso.app_hom]
  have hn := congr_app h (op n)
  simp only [NatTrans.comp_app] at hn
  change _ ≫ _ = 𝟙 _ ≫ _ at hn
  simpa only [pull, Functor.whiskeringRight, Functor.whiskerRight,
    Category.id_comp] using hn

/-- Normalization of the strict pullback/reduction comparison on the shifted and
unshifted summands of the actual mapping cone. Level `n` means exponent `n+1`.
Source: proof (1), exact pullback of the cones and their transitions
(blueprint: definition-completed-inverse-image). -/
def IsStrictPullReduction
    (e : strictRed l E T ⋙ (pull l E f).mapHomologicalComplex (.up ℤ) ≅
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
        (.up ℤ) ⋙ strictRed l E T') : Prop :=
  ∀ (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) (i : ℤ) (n : ℕ),
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map
        (((CochainComplex.mappingCone.inl ((complexPowerMap l E T).app M)).v
          (i+1) i (by omega)).app (op n)) ≫
        ((e.hom.app M).f i).app (op n) =
      ((CochainComplex.mappingCone.inl ((complexPowerMap l E T').app
        (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
          (.up ℤ)).obj M))).v (i+1) i (by omega)).app (op n) ∧
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map
        ((CochainComplex.mappingCone.inr ((complexPowerMap l E T).app M)).f i
          |>.app (op n)) ≫ ((e.hom.app M).f i).app (op n) =
      ((CochainComplex.mappingCone.inr ((complexPowerMap l E T').app
        (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
          (.up ℤ)).obj M))).f i).app (op n)

/-- There is a unique strict comparison preserving both cone summands.
Source: proof (1) (blueprint: definition-completed-inverse-image).
Proof: exact additive pullback commutes with the finite biproduct defining each cone
term. Its coefficient morphism takes multiplication by π to multiplication by π.
The two identity summand maps therefore commute with the cone differential and the
(π,1) transitions. They are natural in the complex and give an isomorphism. The two
summand equations determine its components, hence the whole natural isomorphism. -/
theorem strictPullReduction_existsUnique :
    ∃! e : strictRed l E T ⋙ (pull l E f).mapHomologicalComplex (.up ℤ) ≅
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
        (.up ℤ) ⋙ strictRed l E T', IsStrictPullReduction l E f e := by
  let e := strictCompare l E f
  have hn : IsStrictPullReduction l E f e := by
    intro M i n
    exact ⟨strictCompare_inl l E f M i n, strictCompare_inr l E f M i n⟩
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply HomologicalComplex.Hom.ext
  funext i
  apply ConeNaturality.mapCone_ext (pull l E f) ((complexPowerMap l E T).app M) i
  · apply NatTrans.ext
    funext n
    exact (he' M i n.unop).1.trans (hn M i n.unop).1.symm
  · apply NatTrans.ext
    funext n
    exact (he' M i n.unop).2.trans (hn M i n.unop).2.symm

/-- The strict cone comparison, chosen from its summandwise unique characterization.
Source: proof (1) (blueprint: definition-completed-inverse-image). -/
def strictPullReduction := (strictPullReduction_existsUnique l E f).exists.choose

/-- The localization equation defining the derived pullback/reduction comparison.
Source: proof (1) (blueprint: definition-completed-inverse-image). -/
def IsPullReduction
    (e : red l E T ⋙ dpull l E f ≅ dpullModule l E f ⋙ red l E T') : Prop :=
  ∀ M : CochainComplex (AdicCompletion.Modules l E T) ℤ,
    (dpull l E f).map ((redFactors l E T).inv.app M) ≫
        e.hom.app (DerivedCategory.Q.obj M) ≫
        (red l E T').map
          ((Functor.mapDerivedCategoryFactors
            (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).hom.app M) ≫
        (redFactors l E T').hom.app
          (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
            (.up ℤ)).obj M) =
      (pull l E f).mapDerivedCategoryFactors.hom.app ((strictRed l E T).obj M) ≫
        DerivedCategory.Q.map ((strictPullReduction l E f).hom.app M)

/-- Exact localization descends the strict normalized comparison uniquely.
Source: proof (1) (blueprint: definition-completed-inverse-image).
Proof: both composites invert quasi-isomorphisms, because pullback is exact and the
strict reduction functor inverts quasi-isomorphisms. Descend the strict comparison
and its inverse through the localization Q. Its universal property gives both the
normalization equation and uniqueness. -/
theorem pullReduction_existsUnique :
    ∃! e : red l E T ⋙ dpull l E f ≅ dpullModule l E f ⋙ red l E T',
      IsPullReduction l E f e := by
  let H := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  let F := red l E T ⋙ dpull l E f
  let G := dpullModule l E f ⋙ red l E T'
  let a : DerivedCategory.Q ⋙ F ≅
      strictRed l E T ⋙ (pull l E f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (redFactors l E T) (dpull l E f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (strictRed l E T) (pull l E f).mapDerivedCategoryFactors
  let b : DerivedCategory.Q ⋙ G ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ strictRed l E T' ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight H.mapDerivedCategoryFactors (red l E T') ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (H.mapHomologicalComplex (.up ℤ)) (redFactors l E T')
  let c : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G :=
    a ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (strictPullReduction l E f) DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫ b.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q (C := AdicCompletion.Modules l E T))
    (HomologicalComplex.quasiIso _ (.up ℤ)) (DTow l E T')
  let e : F ≅ G := ff.preimageIso c
  have he (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
      e.hom.app (DerivedCategory.Q.obj M) = c.hom.app M :=
    congr_app (ff.map_preimage c.hom) M
  have hn : IsPullReduction l E f e := by
    intro M
    rw [he]
    dsimp [c, a, b, H]
    simp only [Category.assoc, Category.id_comp, Category.comp_id]
    erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
    erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro M
  apply (cancel_epi ((dpull l E f).map ((redFactors l E T).inv.app M))).1
  apply (cancel_mono ((red l E T').map (H.mapDerivedCategoryFactors.hom.app M) ≫
    (redFactors l E T').hom.app ((H.mapHomologicalComplex (.up ℤ)).obj M))).1
  simpa only [Category.assoc] using (he' M).trans (hn M).symm

/-- The canonical tower isomorphism f* red(M) ≅ red(f*M), not a levelwise choice.
Source: assertion (1) (blueprint: definition-completed-inverse-image). -/
def pullReduction := (pullReduction_existsUnique l E f).exists.choose

/-- Completed inverse image is Rlim of exact pullback of the reduction tower.
Source: the defining display (blueprint: definition-completed-inverse-image). -/
def completedPull := red l E T ⋙ dpull l E f ⋙ rlim l E T'

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
