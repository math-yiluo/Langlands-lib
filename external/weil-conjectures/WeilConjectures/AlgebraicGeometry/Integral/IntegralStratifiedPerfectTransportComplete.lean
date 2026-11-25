/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectTransportProfile
public import WeilConjectures.CategoryTheory.Adjunction.TowerTransitionTransport
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.AlgebraicGeometry.SmoothBaseChange.ActualCompletedReductionReconstruction
import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientCompletionRoosTransport
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulReductionRoosTriangle
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison

/-! # Intrinsic completeness along isomorphisms of coefficient data

The finite reduction towers of a completed object and of its transport along the completed
isomorphism of a datum isomorphism are identified, compatibly with the transitions. A
derived-limit presentation therefore transports, and with the Roos triangle of the
completion reflector it gives intrinsic completeness.

## References

* Stacks Tags 099M and 099N
* Bhatt--Scholze, Proposition 6.6.11
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective

private local instance (priority := 100000) fixedSmall'' (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EssentiallySmall.{u + 1} T.ProEt :=
  CategoryTheory.essentiallySmallSelf.{0} _

private noncomputable local instance (priority := 100000) fixedSheafify''
    (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

private local instance (priority := 100000) fixedLocallyBijective''
    (T : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem restrictComp_apply'
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp a b c h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists a b c h).exists.choose_spec M U x

/-- Associativity of derived restriction comparisons, componentwise. -/
theorem pbcDerivedRestrictComp_assoc_app
    {T : Scheme.{u}} {R S B V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ V)
    (ab : R ⟶ B) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : ab ≫ c = abc) (habc' : a ≫ bc = abc) (Y : DerivedCategory (pbcModules T V)) :
    (pbcDerivedRestrictComp a b ab hab).hom.app ((pbcDerivedRestrict c).obj Y) ≫
        (pbcDerivedRestrictComp ab c abc habc).hom.app Y =
      (pbcDerivedRestrict a).map ((pbcDerivedRestrictComp b c bc hbc).hom.app Y) ≫
        (pbcDerivedRestrictComp a bc abc habc').hom.app Y := by
  have h : Functor.isoWhiskerLeft (pbcDerivedRestrict c) (pbcDerivedRestrictComp a b ab hab) ≪≫
        pbcDerivedRestrictComp ab c abc habc =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pbcDerivedRestrictComp b c bc hbc) (pbcDerivedRestrict a) ≪≫
        pbcDerivedRestrictComp a bc abc habc' := by
    apply SheafOfModules.SuccessiveDerivedQuotient.exactComp_assoc
    apply Iso.ext
    ext M U x
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp]
    change ((pbcRestrictComp ab c abc habc).hom.app M).val.app U
        (((pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M)).val.app U x) =
      ((pbcRestrictComp a bc abc habc').hom.app M).val.app U
        (((pbcRestrictComp b c bc hbc).hom.app M).val.app U x)
    simp only [restrictComp_apply']
  have hY := congrArg (fun e ↦ e.hom.app Y) h
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp] using hY

/-- Mates of isomorphisms between equivalences are isomorphisms. -/
theorem isIso_mateEquiv_symm_of_equivalences
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'}
    (a : L ⊣ R) (b : L' ⊣ R') [G.IsEquivalence] [H.IsEquivalence]
    (β : TwoSquare R H G R') [IsIso β] :
    IsIso ((mateEquiv a b).symm β) := by
  let eG := G.asEquivalence.toAdjunction
  let eH := H.asEquivalence.toAdjunction
  let α := (mateEquiv a b).symm β
  have hi : IsIso (mateEquiv eH eG β) := by
    dsimp only [mateEquiv, Equiv.coe_fn_mk]
    infer_instance
  have he := iterated_mateEquiv_conjugateEquiv a b eG eH α
  change (mateEquiv eH eG ((mateEquiv a b) ((mateEquiv a b).symm β))) = _ at he
  rw [Equiv.apply_symm_apply] at he
  have : IsIso (conjugateEquiv (a.comp eH) (eG.comp b) α) := he ▸ hi
  exact conjugateEquiv_of_iso (a.comp eH) (eG.comp b) α

section Tower

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal) (T : Scheme.{u})

/-- Restriction of completed coefficients along the completed isomorphism. -/
abbrev AdicCoefficientDatum.transportBack :
    PbcCompletedDerived T d' ⥤ PbcCompletedDerived T d :=
  pbcDerivedRestrict (d.completionIso d' φ hφ T).hom

/-- Restriction along a level isomorphism is an equivalence. -/
instance (n : ℕ) : (pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom).IsEquivalence :=
  (pbcDerivedRestrictIsoEquivalence (d.levelIso d' φ hφ T n)).isEquivalence_functor

/-- Restriction along the completed isomorphism is an equivalence. -/
instance : (d.transportBack d' φ hφ T).IsEquivalence :=
  (pbcDerivedRestrictIsoEquivalence (d.completionIso d' φ hφ T)).isEquivalence_functor

/-- The level isomorphisms commute with the quotient maps. -/
theorem AdicCoefficientDatum.levelIso_quotient (n : ℕ) :
    (d.levelIso d' φ hφ T (n + 1)).hom ≫ pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n) =
      pbcAdicQuotient T d (n + 1) n (Nat.le_succ n) ≫ (d.levelIso d' φ hφ T n).hom :=
  ((d.ringSystemHom d' φ hφ T).naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The base change comparison of restrictions to a level. -/
def AdicCoefficientDatum.levelRestrictIso (n : ℕ) :
    pbcDerivedRestrict (pbcAdicProjection T d' n) ⋙ d.transportBack d' φ hφ T ≅
      pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom ⋙
        pbcDerivedRestrict (pbcAdicProjection T d n) :=
  pbcDerivedRestrictComp (d.completionIso d' φ hφ T).hom (pbcAdicProjection T d' n)
      (pbcAdicProjection T d n ≫ (d.levelIso d' φ hφ T n).hom)
      (d.completionIso_hom_projection d' φ hφ T n) ≪≫
    (pbcDerivedRestrictComp (pbcAdicProjection T d n) (d.levelIso d' φ hφ T n).hom _ rfl).symm

/-- The base change comparison of quotient restrictions. -/
def AdicCoefficientDatum.quotientRestrictIso (n : ℕ) :
    pbcDerivedRestrict (pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n)) ⋙
        pbcDerivedRestrict (d.levelIso d' φ hφ T (n + 1)).hom ≅
      pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom ⋙
        pbcDerivedRestrict (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) :=
  pbcDerivedRestrictComp (d.levelIso d' φ hφ T (n + 1)).hom
      (pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n))
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n) ≫ (d.levelIso d' φ hφ T n).hom)
      (d.levelIso_quotient d' φ hφ T n) ≪≫
    (pbcDerivedRestrictComp (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))
      (d.levelIso d' φ hφ T n).hom _ rfl).symm

/-- The base change map of finite reductions, the mate of the restriction comparison. -/
def AdicCoefficientDatum.levelExtendMap (n : ℕ) :
    d.transportBack d' φ hφ T ⋙ pbcDerivedExtend (pbcAdicProjection T d n) ⟶
      pbcDerivedExtend (pbcAdicProjection T d' n) ⋙
        pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom :=
  ((mateEquiv (pbcDerivedScalarAdjunction (pbcAdicProjection T d' n))
    (pbcDerivedScalarAdjunction (pbcAdicProjection T d n))).symm
    (TwoSquare.mk _ _ _ _ (d.levelRestrictIso d' φ hφ T n).hom))

/-- The base change map of reductions is invertible. -/
instance (n : ℕ) : IsIso (d.levelExtendMap d' φ hφ T n) :=
  isIso_mateEquiv_symm_of_equivalences _ _ _

/-- The base change isomorphism of finite reductions. -/
def AdicCoefficientDatum.levelExtendIso (n : ℕ) :
    d.transportBack d' φ hφ T ⋙ pbcDerivedExtend (pbcAdicProjection T d n) ≅
      pbcDerivedExtend (pbcAdicProjection T d' n) ⋙
        pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom :=
  asIso (d.levelExtendMap d' φ hφ T n)

/-- Unit compatibility of the base change isomorphism of reductions. -/
theorem AdicCoefficientDatum.levelExtendIso_unit (n : ℕ) (K : PbcCompletedDerived T d') :
    (d.transportBack d' φ hφ T).map
        ((pbcDerivedScalarAdjunction (pbcAdicProjection T d' n)).unit.app K) ≫
      (d.levelRestrictIso d' φ hφ T n).hom.app
        ((pbcDerivedExtend (pbcAdicProjection T d' n)).obj K) =
    (pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.app
        ((d.transportBack d' φ hφ T).obj K) ≫
      (pbcDerivedRestrict (pbcAdicProjection T d n)).map
        ((d.levelExtendIso d' φ hφ T n).hom.app K) :=
  unit_mateEquiv_symm _ _ (TwoSquare.mk _ _ _ _ (d.levelRestrictIso d' φ hφ T n).hom) K

/-- The finite reduction towers are intertwined by the base change comparisons. -/
theorem AdicCoefficientDatum.tower_baseChange (n : ℕ) (K : PbcCompletedDerived T d') :
    (d.transportBack d' φ hφ T).map
        (Adjunction.towerTransition (pbcDerivedScalarAdjunction (pbcAdicProjection T d' n))
          (pbcDerivedScalarAdjunction (pbcAdicProjection T d' (n + 1)))
          (pbcDerivedRestrictComp (pbcAdicProjection T d' (n + 1))
            (pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d' n)
            (pbcAdicProjection_comp T d' (n + 1) n (Nat.le_succ n))) K) ≫
      (Adjunction.towerBaseChange (d.transportBack d' φ hφ T)
        (pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom)
        (d.levelRestrictIso d' φ hφ T n) (d.levelExtendIso d' φ hφ T n) K).hom =
    (Adjunction.towerBaseChange (d.transportBack d' φ hφ T)
        (pbcDerivedRestrict (d.levelIso d' φ hφ T (n + 1)).hom)
        (d.levelRestrictIso d' φ hφ T (n + 1)) (d.levelExtendIso d' φ hφ T (n + 1)) K).hom ≫
      Adjunction.towerTransition (pbcDerivedScalarAdjunction (pbcAdicProjection T d n))
          (pbcDerivedScalarAdjunction (pbcAdicProjection T d (n + 1)))
          (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)))
          ((d.transportBack d' φ hφ T).obj K) := by
  refine Adjunction.towerTransition_baseChange _ _ _ _ _ _ _ _ _ _ _
    (d.quotientRestrictIso d' φ hφ T n) _ _
    (d.levelExtendIso_unit d' φ hφ T n) (d.levelExtendIso_unit d' φ hφ T (n + 1)) ?_ K
  intro Y
  let ρh := (d.completionIso d' φ hφ T).hom
  let a1 := pbcAdicProjection T d' (n + 1)
  let q' := pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n)
  let p' := pbcAdicProjection T d' n
  let P1 := pbcAdicProjection T d (n + 1)
  let q := pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)
  let Pn := pbcAdicProjection T d n
  let l1 := (d.levelIso d' φ hφ T (n + 1)).hom
  let lh := (d.levelIso d' φ hφ T n).hom
  have h1 : ρh ≫ a1 = P1 ≫ l1 := d.completionIso_hom_projection d' φ hφ T (n + 1)
  have h2 : a1 ≫ q' = p' := pbcAdicProjection_comp T d' (n + 1) n (Nat.le_succ n)
  have h4 : ρh ≫ p' = Pn ≫ lh := d.completionIso_hom_projection d' φ hφ T n
  have hq : P1 ≫ q = Pn := pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)
  have hl : l1 ≫ q' = q ≫ lh := d.levelIso_quotient d' φ hφ T n
  have h3 : (P1 ≫ l1) ≫ q' = Pn ≫ lh := by rw [Category.assoc, hl, ← Category.assoc, hq]
  have h5 : P1 ≫ (q ≫ lh) = Pn ≫ lh := by rw [← Category.assoc, hq]
  have A1 := pbcDerivedRestrictComp_assoc_app ρh a1 q' (P1 ≫ l1) p' (Pn ≫ lh) h1 h2 h3 h4 Y
  have A2 := pbcDerivedRestrictComp_assoc_app P1 l1 q' (P1 ≫ l1) (q ≫ lh) (Pn ≫ lh) rfl hl h3 h5 Y
  have A3 := pbcDerivedRestrictComp_assoc_app P1 q lh Pn (q ≫ lh) (Pn ≫ lh) hq rfl rfl h5 Y
  have A2' : (pbcDerivedRestrictComp (P1 ≫ l1) q' (Pn ≫ lh) h3).hom.app Y =
      (pbcDerivedRestrictComp P1 l1 (P1 ≫ l1) rfl).inv.app ((pbcDerivedRestrict q').obj Y) ≫
        (pbcDerivedRestrict P1).map ((pbcDerivedRestrictComp l1 q' (q ≫ lh) hl).hom.app Y) ≫
        (pbcDerivedRestrictComp P1 (q ≫ lh) (Pn ≫ lh) h5).hom.app Y := by
    rw [← A2, Iso.inv_hom_id_app_assoc]
  have A3' : (pbcDerivedRestrictComp P1 (q ≫ lh) (Pn ≫ lh) h5).hom.app Y =
      (pbcDerivedRestrict P1).map ((pbcDerivedRestrictComp q lh (q ≫ lh) rfl).inv.app Y) ≫
        (pbcDerivedRestrictComp P1 q Pn hq).hom.app ((pbcDerivedRestrict lh).obj Y) ≫
        (pbcDerivedRestrictComp Pn lh (Pn ≫ lh) rfl).hom.app Y := by
    rw [A3, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  simp only [levelRestrictIso, quotientRestrictIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% A1, A2', A3']
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]

end Tower

section Complete

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal) (T : Scheme.{u})

private theorem complete_of_iso' {T : Scheme.{u}} {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) {M N : PbcCompletedDerived T e} (i : M ≅ N)
    (hM : PbcIsIntrinsicallyComplete T e M) : PbcIsIntrinsicallyComplete T e N := by
  obtain ⟨r, a, ha, C, eC, hC⟩ := hM
  refine ⟨r, a, ha, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison T e).inv).mapIso i, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

/-- A derived-limit presentation of an object by its reduction tower makes it complete. -/
private theorem complete_of_reduction_derivedLimit {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) (K : PbcCompletedDerived T e)
    [HasProduct (fun n ↦ (WeilConjectures.IntegralCoefficientPresentation.reduction
      (pbcAdicProjection T e n)).obj K)]
    (p : K ⟶ ∏ᶜ fun n ↦ (WeilConjectures.IntegralCoefficientPresentation.reduction
      (pbcAdicProjection T e n)).obj K)
    (δ : (∏ᶜ fun n ↦ (WeilConjectures.IntegralCoefficientPresentation.reduction
      (pbcAdicProjection T e n)).obj K) ⟶ K⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle (fun n ↦ (reconstructionStep T e n).app K) K p δ) :
    PbcIsIntrinsicallyComplete T e K := by
  obtain ⟨hp, p', δ', h', -⟩ := WeilConjectures.pbcNormalizedRoos T e K
  let T₁ := Pretriangulated.Triangle.mk p
    (towerTransitionEndomorphism (fun n ↦ (reconstructionStep T e n).app K)) δ
  let T₂ := Pretriangulated.Triangle.mk p'
    (towerTransitionEndomorphism (fun n ↦ (reconstructionStep T e n).app K)) δ'
  obtain ⟨a, ha₁, ha₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁ T₁ T₂ h h'
    (𝟙 _) (𝟙 _) (by simp [T₁, T₂])
  let ψ : T₁ ⟶ T₂ :=
    { hom₁ := a
      hom₂ := 𝟙 _
      hom₃ := 𝟙 _
      comm₁ := by simpa using ha₁
      comm₂ := by simp [T₁, T₂]
      comm₃ := by simpa using ha₃ }
  have : IsIso a := Pretriangulated.isIso₁_of_isIso₂₃ ψ h h' (by dsimp [ψ]; infer_instance)
    (by dsimp [ψ]; infer_instance)
  exact complete_of_iso' e (asIso a).symm
    ((ObjectProperty.ι (PbcIsIntrinsicallyComplete T e)).leftAdjoint.obj K).property

/-- Intrinsic completeness transports along an isomorphism of coefficient data. -/
theorem AdicCoefficientDatum.transport_intrinsicallyComplete (K : PbcCompletedDerived T d)
    (hK : PbcIsIntrinsicallyComplete T d K) :
    PbcIsIntrinsicallyComplete T d' ((d.transportDerived d' φ hφ T).obj K) := by
  classical
  let Ψ := d.transportBack d' φ hφ T
  let K' := (d.transportDerived d' φ hφ T).obj K
  let K₀ := Ψ.obj K'
  let r := (pbcDerivedRestrictIsoEquivalence (d.completionIso d' φ hφ T)).counitIso.app K
  have hK₀ : PbcIsIntrinsicallyComplete T d K₀ := complete_of_iso' d r.symm hK
  let := WeilConjectures.IntegralCoefficientPresentation.derived_products T
    (pbcAdicCompletion T d)
  let := WeilConjectures.IntegralCoefficientPresentation.derived_products T
    (pbcAdicCompletion T d')
  have hlim := pbc_actual_completed_reduction_reconstruction T d K₀ hK₀
  have hlim' : IsDerivedLimit (K := fun n ↦ (pbcCompletedReduction T d n ⋙
      pbcDerivedRestrict (pbcAdicProjection T d n)).obj K₀)
      (fun n ↦ (reconstructionStep T d n).app K₀) K₀ := by
    refine reconstructionLimit_transport _ _ K₀ hlim (fun n ↦ Iso.refl _) (fun n ↦ ?_)
    simp only [Functor.ofOpSequence_map_homOfLE_succ, Iso.refl_hom, Category.comp_id,
      Category.id_comp]
    rfl
  obtain ⟨p', δ', h'⟩ := hlim'
  let a (n : ℕ) := Adjunction.towerBaseChange Ψ
    (pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom)
    (d.levelRestrictIso d' φ hφ T n) (d.levelExtendIso d' φ hφ T n) K'
  let F := (pbcRestrict (d.completionIso d' φ hφ T).hom).mapDerivedCategory
  have : F.IsEquivalence :=
    (pbcDerivedRestrictIsoEquivalence (d.completionIso d' φ hφ T)).isEquivalence_functor
  obtain ⟨p, δ, h, -⟩ := reflectNormalizedRoos F
    (V := fun n ↦ (pbcCompletedReduction T d' n ⋙
      pbcDerivedRestrict (pbcAdicProjection T d' n)).obj K')
    (W := fun n ↦ (pbcCompletedReduction T d n ⋙
      pbcDerivedRestrict (pbcAdicProjection T d n)).obj K₀) a
    (fun n ↦ (reconstructionStep T d' n).app K') (fun n ↦ (reconstructionStep T d n).app K₀)
    (fun n ↦ d.tower_baseChange d' φ hφ T n K') (Iso.refl K₀) p' δ' h' (𝟙 K')
    (fun n ↦ F.preimage (p' ≫ Pi.π _ n ≫ (a n).inv)) (fun n ↦ by
      rw [Functor.map_preimage]
      simp only [Iso.refl_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [CategoryTheory.Functor.map_id]
      exact (Category.id_comp _).trans (Category.id_comp (p' ≫ Pi.π _ n)))
  exact complete_of_reduction_derivedLimit T d' K' p δ h

end Complete

/-- The implication "intrinsically complete with a uniform reduction profile implies
stratified perfect" is invariant under isomorphisms of adic coefficient data. -/
theorem isIntegralStratifiedPerfect_of_ringEquiv (T : Scheme.{u})
    {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
    (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)
    (h' : ∀ K' : PbcCompletedDerived T d', PbcIsIntrinsicallyComplete T d' K' →
      PbcUniformReductionProfile T d' K' → IsIntegralStratifiedPerfect T d' K')
    (K : PbcCompletedDerived T d) (hc : PbcIsIntrinsicallyComplete T d K)
    (hp : PbcUniformReductionProfile T d K) :
    IsIntegralStratifiedPerfect T d K :=
  d.isIntegralStratifiedPerfect_of_transport d' φ hφ T K
    (h' _ (d.transport_intrinsicallyComplete d' φ hφ T K hc)
      (d.transport_uniformReductionProfile d' φ hφ T K hp))

end AlgebraicGeometry.Scheme
