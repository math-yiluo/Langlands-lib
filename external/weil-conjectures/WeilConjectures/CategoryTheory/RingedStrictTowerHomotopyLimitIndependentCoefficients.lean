/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Total derived inverse limits with independent site and coefficient universes

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941; More on Algebra,
Tag 0H9L (auxiliary; not a blueprint node).

This companion retains the original interface through its public import. Its generalized
statement applies to the small pro-etale site and the actual completed coefficient sheaf.
-/

@[expose] public section

set_option autoImplicit false

universe w uC vC r u v u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped BigOperators

namespace CategoryTheory

private lemma totalDerivedData {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    ∃ (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w'} B)
      (η : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RF),
      RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) ∧
      ∃ (_ : RF.CommShift ℤ), RF.IsTriangulated := by
  let π := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let H := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let RF := F.rightDerivedFunctor
  let e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  let η : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
    e.hom ≫ Functor.whiskerLeft π F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) RF).hom
  have hi (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (η.app I) := by
    dsimp [η]
    infer_instance
  refine ⟨RF, η, ?_, fun I hI ↦ hi I, inferInstance, inferInstance⟩
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := by
    intro I J f hf
    have : IsIso (CochainComplex.KInjectives.toHomotopyCategory.map f) :=
      (CochainComplex.KInjectives.isIso_toHomotopyCategory_map_iff f).mpr hf
    have hmap := (HomotopyCategory.KInjectives.ι ⋙ H).map_isIso
      (CochainComplex.KInjectives.toHomotopyCategory.map f)
    have hmap' : IsIso ((π ⋙ H).map f.hom) := hmap
    have heq : (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).map f.hom = e.hom.app I.obj ≫
          (π ⋙ H).map f.hom ≫ e.inv.app J.obj := by
      rw [← e.hom.naturality_assoc]
      simp
    change IsIso ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).map f.hom)
    rw [heq]
    infer_instance
  exact h.isRightDerivedFunctor_of_isIso η (fun I ↦ by
    have := I.property
    exact hi I.obj)

private lemma moduleSheaves_grothendieck
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] (R : Sheaf J RingCat.{r}) :
    IsGrothendieckAbelian.{r} (SheafOfModules.{r} R) := by
  let e := equivSmallModel.{r} C
  let K := e.inverse.inducedTopology J
  let R' : Sheaf K RingCat.{r} :=
    (e.inverse.sheafPushforwardContinuous RingCat.{r} K J).obj R
  let φ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{r} J K).obj R' :=
    ⟨Functor.whiskerRight (NatTrans.op e.unitInv) R.obj⟩
  let ψ : R' ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{r} K J).obj R := 𝟙 _
  have h₁ : Functor.whiskerRight (NatTrans.op e.counit) R'.obj =
      ψ.hom ≫ e.inverse.op.whiskerLeft φ.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map (e.inverse.map (e.counit.app U.unop)).op =
      R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op
    rw [e.unitInv_app_inverse]
  have h₂ : φ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) R.obj = 𝟙 R.obj := by
    apply NatTrans.ext
    funext U
    change R.obj.map (e.unitInv.app U.unop).op ≫
      (𝟙 _ ≫ R.obj.map (e.unit.app U.unop).op) = 𝟙 _
    rw [Category.id_comp, ← R.obj.map_comp, ← op_comp, e.unitIso.hom_inv_id_app]
    exact R.obj.map_id _
  let E := SheafOfModules.pushforwardPushforwardEquivalence.{r} e φ ψ h₁ h₂
  have : IsGrothendieckAbelian.{r} (SheafOfModules.{r} R') :=
    SheafOfModules.isGrothendieckAbelian R'
  exact IsGrothendieckAbelian.of_equivalence E

private lemma tower_grothendieck
    (A : Type uC) [Category.{vC} A] [Abelian A] [IsGrothendieckAbelian.{r} A] :
    IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

private theorem evaluationData
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] :
    ∃ (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A)),
      Nonempty (DerivedCategory.Q.{w} ⋙ E ≅
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
          (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
            (DerivedCategory.{w} A)).obj DerivedCategory.Q.{w}) := by
  let H : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A) :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
        (DerivedCategory.{w} A)).obj DerivedCategory.Q.{w}
  have h : (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)).IsInvertedBy H := by
    intro X Y f hf
    have : QuasiIso f := hf
    have : ∀ n, IsIso ((H.map f).app n) := by
      intro n
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (ComplexShape.up ℤ)).map f))
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact ⟨Localization.lift H h DerivedCategory.Q, ⟨Localization.fac H h DerivedCategory.Q⟩⟩

private theorem derivedCountableProducts
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [CategoryTheory.Abelian.HasKInjectiveResolutions A] [HasCountableProducts A] :
    HasCountableProducts (DerivedCategory.{w} A) := by
  exact ⟨fun J _ ↦ DerivedCategory.hasLimitsOfShape_discrete A J⟩

private lemma proZero_transition_iso
    {A : Type uC} [Category.{vC} A] [Preadditive A] (K : ℕᵒᵖ ⥤ A)
    [HasProduct (fun n : ℕ ↦ K.obj (op n))]
    (hz : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), K.map (homOfLE h).op = 0) :
    IsIso (towerTransitionEndomorphism (K := fun n : ℕ ↦ K.obj (op n))
      (fun n : ℕ ↦ K.map (homOfLE (Nat.le_succ n)).op)) := by
  classical
  let X := fun n : ℕ ↦ K.obj (op n)
  let P := ∏ᶜ X
  let s : P ⟶ P := towerProductShift
    (fun n : ℕ ↦ K.map (homOfLE (Nat.le_succ n)).op)
  have hs (n : ℕ) : s ≫ Pi.π X n =
      Pi.π X (n + 1) ≫ K.map (homOfLE (Nat.le_succ n)).op := Pi.lift_comp_π _ _
  have hp (k n : ℕ) : ((End.of s ^ k).asHom) ≫ Pi.π X n =
      Pi.π X (n + k) ≫ K.map (homOfLE (Nat.le_add_right n k)).op := by
    induction k generalizing n with
    | zero =>
      rw [pow_zero, End.one_asHom, Category.id_comp]
      exact (Category.comp_id _).symm.trans (by congr 1; exact (K.map_id _).symm)
    | succ k ih =>
      rw [pow_succ, End.mul_asHom, Category.assoc, ih, ← Category.assoc, hs]
      rw [Category.assoc, ← K.map_comp]
      rfl
  have hn (n : ℕ) : ∃ k : ℕ, (End.of s ^ k).asHom ≫ Pi.π X n = 0 := by
    obtain ⟨m, h, hm⟩ := hz n
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨k, ?_⟩
    rw [hp, hm, comp_zero]
  choose b hb using hn
  let k : ℕ → ℕ := Nat.rec (b 0) (fun n a ↦ max a (b (n + 1)))
  have hbk (n : ℕ) : b n ≤ k n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  have hkk (n : ℕ) : k n ≤ k (n + 1) := le_max_left _ _
  have hv (n i : ℕ) (hi : b n ≤ i) : (End.of s ^ i).asHom ≫ Pi.π X n = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [pow_add, End.mul_asHom, Category.assoc, hb, comp_zero]
  let g (l : ℕ) : P ⟶ P := ∑ i ∈ Finset.range l, End.asHom (End.of s ^ i)
  have hg (l : ℕ) : g l ≫ (𝟙 P - s) = 𝟙 P - End.asHom (End.of s ^ l) := by
    induction l with
    | zero => simp [g]
    | succ l ih =>
      simp only [g, Finset.sum_range_succ] at *
      rw [Preadditive.add_comp, ih, Preadditive.comp_sub, Category.comp_id]
      have hpow : (End.of s ^ l).asHom ≫ s = (End.of s ^ (l + 1)).asHom := by
        rw [pow_succ', End.mul_asHom]
      rw [hpow]
      simp only [sub_add_sub_cancel]
  have hg' (l : ℕ) : (𝟙 P - s) ≫ g l = 𝟙 P - End.asHom (End.of s ^ l) := by
    induction l with
    | zero => simp [g]
    | succ l ih =>
      simp only [g, Finset.sum_range_succ] at *
      rw [Preadditive.comp_add, ih, Preadditive.sub_comp, Category.id_comp]
      have hpow : s ≫ (End.of s ^ l).asHom = (End.of s ^ (l + 1)).asHom := by
        rw [pow_succ, End.mul_asHom]
      rw [hpow]
      simp only [sub_add_sub_cancel]
  have hstable (n l l' : ℕ) (hl : b n ≤ l) (hll : l ≤ l') :
      g l ≫ Pi.π X n = g l' ≫ Pi.π X n := by
    simp only [g, Preadditive.sum_comp]
    apply Finset.sum_subset (Finset.range_mono hll)
    intro i hi hi'
    exact hv n i (by have := (Finset.mem_range.not.mp hi'); omega)
  let t : P ⟶ P := Pi.lift (fun n ↦ g (k n) ≫ Pi.π X n)
  have ht (n : ℕ) : t ≫ Pi.π X n = g (k n) ≫ Pi.π X n := Pi.lift_comp_π _ _
  refine ⟨t, ?_, ?_⟩
  · change (𝟙 P - s) ≫ t = 𝟙 P
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, ht, ← Category.assoc, hg']
    rw [Preadditive.sub_comp, Category.id_comp, hv n (k n) (hbk n), sub_zero]
  · change t ≫ (𝟙 P - s) = 𝟙 P
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub]
    rw [ht, hs, ← Category.assoc, ht, Category.assoc, ← hs]
    rw [hstable n (k n) (k (n + 1)) (hbk n) (hkk n)]
    rw [← Preadditive.comp_sub]
    have hid : Pi.π X n - s ≫ Pi.π X n = (𝟙 P - s) ≫ Pi.π X n := by
      rw [Preadditive.sub_comp, Category.id_comp]
    rw [hid, ← Category.assoc, hg]
    rw [Preadditive.sub_comp, Category.id_comp,
      hv n (k (n + 1)) ((hbk n).trans (hkk n)), sub_zero]

private theorem injective_tower_transition_split
    {A : Type*} [Category A] [Abelian A]
    (T : ℕᵒᵖ ⥤ A) [Injective T]
    (n : ℕ) : IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op) := by
  classical
  let k := (homOfLE (Nat.le_succ n)).op
  let M := T.obj (op n)
  let L := (evaluationLeftAdjoint A (op n)).obj M
  let L' := (evaluationLeftAdjoint A (op (n + 1))).obj M
  let i : L ⟶ L' :=
    { app := fun m ↦ Sigma.desc fun g ↦ Sigma.ι (fun _ ↦ M) (k ≫ g)
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, L', evaluationLeftAdjoint, Category.assoc] }
  have (m : ℕᵒᵖ) : Mono (i.app m) := by
    let r : L'.obj m ⟶ L.obj m := Sigma.desc fun _ ↦
      if h : Nonempty (op n ⟶ m) then Sigma.ι (fun _ ↦ M) h.some else 0
    have hr : i.app m ≫ r = 𝟙 _ := by
      apply Sigma.hom_ext
      intro g
      simp only [i, r, colimit.ι_desc_assoc, Cofan.mk_ι_app,
        dite_eq_left (show Nonempty (op n ⟶ m) from ⟨g⟩), colimit.ι_desc]
      exact (congrArg (Sigma.ι (fun _ : op n ⟶ m ↦ M))
        (Subsingleton.elim _ g)).trans (Category.comp_id _).symm
    exact (IsSplitMono.mk' ⟨r, hr⟩).mono
  have : Mono i := NatTrans.mono_of_mono_app i
  let a : L ⟶ T :=
    { app := fun m ↦ Sigma.desc fun g ↦ T.map g
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, evaluationLeftAdjoint, Functor.map_comp] }
  let b := Injective.factorThru a i
  have hb : i ≫ b = a := Injective.comp_factorThru a i
  refine IsSplitEpi.mk' ⟨Sigma.ι (fun _ ↦ M) (𝟙 (op (n + 1))) ≫
    b.app (op (n + 1)), ?_⟩
  rw [Category.assoc, ← b.naturality k, ← Category.assoc]
  have hn := congrArg (fun f : L ⟶ T ↦
    Sigma.ι (fun _ ↦ M) (𝟙 (op n)) ≫ f.app (op n)) hb
  simpa [L', evaluationLeftAdjoint, i, a] using hn

private theorem tower_compatibility
    {B : Type*} [Category* B] (F : ℕᵒᵖ ⥤ B) {Z : B}
    (a : ∀ n : ℕ, Z ⟶ F.obj (Opposite.op n))
    (ha : ∀ n, a (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = a n)
    {n m : ℕ} (h : n ≤ m) : a m ≫ F.map (homOfLE h).op = a n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    have he : (homOfLE (Nat.le_trans h (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, F.map_comp, ← Category.assoc, ha, ih]

private theorem tower_kernel
    {B : Type*} [Category* B] [Preadditive B]
    (F : ℕᵒᵖ ⥤ B) (c : Cone F) (hc : IsLimit c)
    (P : Fan (fun n : ℕ ↦ F.obj (Opposite.op n))) (hP : IsLimit P)
    (i : c.pt ⟶ P.pt) (t : P.pt ⟶ P.pt)
    (hi : ∀ n : ℕ, i ≫ P.proj n = c.π.app (Opposite.op n))
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj n -
      P.proj (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) :
    ∃ h : i ≫ t = 0, Nonempty (IsLimit (KernelFork.ofι i h)) := by
  have hz : i ≫ t = 0 := by
    apply hP.hom_ext
    intro ⟨n⟩
    change (i ≫ t) ≫ P.proj n = 0 ≫ P.proj n
    rw [Category.assoc, ht, Preadditive.comp_sub, hi, ← Category.assoc, hi]
    simp only [zero_comp, sub_eq_zero]
    exact (c.w (homOfLE (Nat.le_succ n)).op).symm
  refine ⟨hz, ⟨Fork.IsLimit.mk' _ ?_⟩⟩
  intro s
  let Z := s.pt
  let k := s.ι
  have hk : k ≫ t = 0 := by
    have h := s.condition
    simp only [comp_zero] at h
    exact h
  have ha (n : ℕ) : (k ≫ P.proj (n + 1)) ≫
      F.map (homOfLE (Nat.le_succ n)).op = k ≫ P.proj n := by
    have hn := congrArg (fun f ↦ f ≫ P.proj n) hk
    rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc, zero_comp] at hn
    exact (sub_eq_zero.mp hn).symm
  let d : Cone F :=
    { pt := Z
      π := { app := fun n ↦ k ≫ P.proj n.unop
             naturality := by
               intro n m f
               change 𝟙 Z ≫ (k ≫ P.proj m.unop) =
                 (k ≫ P.proj n.unop) ≫ F.map f
               rw [Category.id_comp]
               symm
               exact tower_compatibility F (fun n ↦ k ≫ P.proj n) ha
                 (leOfHom f.unop) } }
  refine ⟨hc.lift d, ?_, ?_⟩
  · apply hP.hom_ext
    intro ⟨n⟩
    change (hc.lift d ≫ i) ≫ P.proj n = k ≫ P.proj n
    rw [Category.assoc, hi]
    exact hc.fac d (Opposite.op n)
  · intro l hl
    apply hc.hom_ext
    intro n
    change l ≫ i = k at hl
    calc
      l ≫ c.π.app n = k ≫ P.proj n.unop := by
        rw [← hi n.unop, ← Category.assoc, hl]
      _ = hc.lift d ≫ c.π.app n := (hc.fac d n).symm

private theorem fan_shift_splitEpi
    {A : Type u} [Category.{v} A] [Preadditive A]
    (K : ℕ → A) (P : Fan K) (hP : IsLimit P) (q : ∀ n, K (n + 1) ⟶ K n)
    [∀ n, IsSplitEpi (q n)] (t : P.pt ⟶ P.pt)
    (ht : ∀ n, t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫ q n) : IsSplitEpi t := by
  let a : ∀ n : ℕ, P.pt ⟶ K n := fun n ↦ Nat.rec 0
    (fun n a ↦ (a - P.proj n) ≫ section_ (q n)) n
  have ha (n : ℕ) : a (n + 1) ≫ q n = a n - P.proj n := by
    change ((a n - P.proj n) ≫ section_ (q n)) ≫ q n = _
    rw [Category.assoc, IsSplitEpi.id, Category.comp_id]
  let r := hP.lift (Fan.mk P.pt a)
  have hr (n) : r ≫ P.proj n = a n := hP.fac _ ⟨n⟩
  refine IsSplitEpi.mk' ⟨r, ?_⟩
  apply Fan.IsLimit.hom_ext hP
  intro n
  rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc, hr, hr, ha]
  simp

private theorem complexRoos_shortExact
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [∀ p, Injective (I.X p)] :
    let L := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)
    let p : L.obj I ⟶ ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n)) :=
      Pi.lift (fun n : ℕ ↦ (NatTrans.mapHomologicalComplex
        (lim.π (op n)) (ComplexShape.up ℤ)).app I)
    let t := towerTransitionEndomorphism
      (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
    ∃ h : p ≫ t = 0, (ShortComplex.mk p t h).ShortExact := by
  intro L p t
  let c : Cone I.asFunctor :=
    { pt := L.obj I
      π := { app := fun n ↦ (NatTrans.mapHomologicalComplex
                (lim.π n) (ComplexShape.up ℤ)).app I
             naturality := by
               intro n m f
               ext r
               change 𝟙 _ ≫ limit.π (I.X r) m =
                 limit.π (I.X r) n ≫ (I.X r).map f
               rw [Category.id_comp]
               exact (limit.w _ _).symm } }
  have hc : IsLimit c := by
    apply HomologicalComplex.isLimitOfEval
    intro r
    exact limit.isLimit (I.X r)
  let K := fun n : ℕ ↦ I.asFunctor.obj (op n)
  let P : Fan K := limit.cone (Discrete.functor K)
  have ht (n) : t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫
      I.asFunctor.map (homOfLE (Nat.le_succ n)).op := by
    change t ≫ Pi.π K n = Pi.π K n - Pi.π K (n + 1) ≫ _
    simp [t, K, towerTransitionEndomorphism, towerProductShift]
  obtain ⟨h, ⟨hk⟩⟩ := tower_kernel I.asFunctor c hc P
    (limit.isLimit _) p t (fun n ↦ Pi.lift_comp_π _ n) ht
  refine ⟨h, HomologicalComplex.shortExact_of_degreewise_shortExact _ ?_⟩
  intro r
  let ev := HomologicalComplex.eval A (ComplexShape.up ℤ) r
  have hkr := KernelFork.mapIsLimit _ hk ev
  have hPr : IsLimit (Fan.mk (P.pt.X r) (fun n ↦ (P.proj n).f r)) :=
    (Fan.isLimitMapConeEquiv ev K P) (isLimitOfPreserves ev (limit.isLimit _))
  have (n : ℕ) : IsSplitEpi ((I.X r).map (homOfLE (Nat.le_succ n)).op) :=
    injective_tower_transition_split (I.X r) n
  have htr : IsSplitEpi (t.f r) := fan_shift_splitEpi
    (fun n : ℕ ↦ (I.X r).obj (op n)) _ hPr
    (fun n : ℕ ↦ (I.X r).map (homOfLE (Nat.le_succ n)).op) (t.f r)
    (fun n ↦ congrArg (fun f ↦ f.f r) (ht n))
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hkr)
    (mono_of_isLimit_fork hkr) htr.epi

namespace CoreWork
universe g
set_option backward.isDefEq.respectTransparency false
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]

@[reducible] private noncomputable def L : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)

@[reducible] private noncomputable def P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj I := ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n))
  map f := Limits.Pi.map (fun n : ℕ ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))
  map_id I := by
    apply Pi.hom_ext
    intro n
    simp only [Limits.Pi.map_π, Category.id_comp]
    exact Category.comp_id _
  map_comp f g := by simp [Limits.Pi.map_comp_map]

@[reducible] private noncomputable def inc : L (A := A) ⟶ P where
  app I := Pi.lift (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app I)
  naturality I J f := by
    apply Pi.hom_ext
    intro n
    simp only [P, Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    exact (NatTrans.mapHomologicalComplex (lim.π (op n))
      (ComplexShape.up ℤ)).naturality f

@[reducible] private noncomputable def diff : P (A := A) ⟶ P where
  app I := towerTransitionEndomorphism
    (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
  naturality I J f := by
    dsimp only [P]
    apply towerTransitionEndomorphism_natural_backward
    intro n
    exact ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).naturality
      (homOfLE (Nat.le_succ n)).op).symm

private lemma inc_diff (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    inc.app I ≫ diff.app I = 0 := by
  change (Pi.lift (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app I)) ≫
    towerTransitionEndomorphism _ = 0
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Category.assoc,
    Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
    Pi.lift_comp_π, Pi.lift_comp_π_assoc, zero_comp, sub_eq_zero]
  ext r
  exact (limit.w (I.X r) (homOfLE (Nat.le_succ n)).op).symm

@[reducible] private noncomputable def S (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ShortComplex (CochainComplex A ℤ) := ShortComplex.mk (inc.app I) (diff.app I) (inc_diff I)

private lemma hS (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [∀ r, Injective (I.X r)] :
    (S I).ShortExact := by
  obtain ⟨h, hs⟩ := complexRoos_shortExact I
  exact hs

@[reducible] private noncomputable def Smap {I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : I ⟶ J) : S I ⟶ S J :=
  { τ₁ := L.map f
    τ₂ := P.map f
    τ₃ := P.map f
    comm₁₂ := inc.naturality f
    comm₂₃ := diff.naturality f }

variable [HasDerivedCategory.{w} A] [HasCountableProducts (DerivedCategory.{w} A)]

@[reducible] private noncomputable def DP :
    (ℕᵒᵖ ⥤ DerivedCategory.{w} A) ⥤ DerivedCategory.{w} A where
  obj T := ∏ᶜ (fun n : ℕ ↦ T.obj (op n))
  map f := Limits.Pi.map (fun n : ℕ ↦ f.app (op n))
  map_id T := by
    apply Pi.hom_ext
    intro n
    simp only [NatTrans.id_app, Limits.Pi.map_π, Category.id_comp, Category.comp_id]
  map_comp f g := by simp [Limits.Pi.map_comp_map]

@[reducible] private noncomputable def evQ : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤
    (ℕᵒᵖ ⥤ DerivedCategory.{w} A) :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
      (DerivedCategory.{w} A)).obj DerivedCategory.Q

@[reducible] private noncomputable def pc : P (A := A) ⋙ DerivedCategory.Q ⟶ evQ ⋙ DP where
  app I := piComparison DerivedCategory.Q (fun n : ℕ ↦ I.asFunctor.obj (op n))
  naturality I J f := by
    apply Pi.hom_ext
    intro n
    change (DerivedCategory.Q.map (P.map f) ≫
      piComparison DerivedCategory.Q (fun n : ℕ ↦ J.asFunctor.obj (op n))) ≫
        Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (J.asFunctor.obj (op n))) n =
      (piComparison DerivedCategory.Q (fun n : ℕ ↦ I.asFunctor.obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ DerivedCategory.Q.map
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)))) ≫
            Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (J.asFunctor.obj (op n))) n
    rw [Category.assoc, piComparison_comp_π, Category.assoc]
    erw [Limits.Pi.map_π]
    rw [← Category.assoc, piComparison_comp_π, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp]
    congr 1
    exact Limits.Pi.map_π (fun k : ℕ ↦
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op k)) n

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma pc_isIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    IsIso (pc.app I : DerivedCategory.Q.obj (P.obj I) ⟶ _) := by
  have (n : ℕ) : CochainComplex.IsKInjective (I.asFunctor.obj (op n)) :=
    tower_evaluation_isKInjective A I (op n)
  let K := fun n : ℕ ↦ I.asFunctor.obj (op n)
  obtain ⟨hki, ⟨hp⟩⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit K
  let P₀ := HomologicalComplex.coneOfHasLimitEval (Discrete.functor K)
  let e : P₀ ≅ limit.cone (Discrete.functor K) :=
    (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor K)).uniqueUpToIso
      (limit.isLimit _)
  have hp' : IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor K))) :=
    IsLimit.ofIsoLimit hp ((Cone.functoriality _ _).mapIso e)
  have hf : IsLimit (Fan.mk (DerivedCategory.Q.obj (P.obj I))
      (fun n : ℕ ↦ DerivedCategory.Q.map (Pi.π K n))) :=
    (Fan.isLimitMapConeEquiv DerivedCategory.Q K (limit.cone _)) hp'
  have he : pc.app I = (IsLimit.conePointUniqueUpToIso hf (productIsProduct _)).hom := by
    apply Pi.hom_ext
    intro n
    exact (piComparison_comp_π _ _ n).trans
      (IsLimit.conePointUniqueUpToIso_hom_comp hf (productIsProduct _) ⟨n⟩).symm
  rw [he]
  infer_instance

@[reducible] private noncomputable def dDP : DP (A := A) ⟶ DP where
  app T := towerTransitionEndomorphism
    (fun n : ℕ ↦ T.map (homOfLE (Nat.le_succ n)).op)
  naturality T U f := by
    dsimp only [DP]
    apply towerTransitionEndomorphism_natural_backward
    intro n
    exact (f.naturality (homOfLE (Nat.le_succ n)).op).symm

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma pc_diff (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.map (diff.app I) ≫ pc.app I = pc.app I ≫ dDP.app (evQ.obj I) := by
  apply Pi.hom_ext
  intro n
  change (DerivedCategory.Q.map (diff.app I) ≫ piComparison DerivedCategory.Q
      (fun n : ℕ ↦ I.asFunctor.obj (op n))) ≫
      Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n))) n =
    (piComparison DerivedCategory.Q (fun n : ℕ ↦ I.asFunctor.obj (op n)) ≫
      towerTransitionEndomorphism (fun n : ℕ ↦ DerivedCategory.Q.map
        (I.asFunctor.map (homOfLE (Nat.le_succ n)).op))) ≫
      Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n))) n
  rw [Category.assoc, piComparison_comp_π, ← DerivedCategory.Q.map_comp]
  have ht : diff.app I ≫ Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n =
      Pi.π _ n - Pi.π _ (n + 1) ≫
        I.asFunctor.map (homOfLE (Nat.le_succ n)).op := by
    simp [towerTransitionEndomorphism, towerProductShift]
  rw [ht, Functor.map_sub, Functor.map_comp]
  simp [towerTransitionEndomorphism, towerProductShift, Category.assoc]

variable [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

private noncomputable abbrev F := CochainComplex.kInjectiveResolutionFunctor.{g} (ℕᵒᵖ ⥤ A)
private noncomputable abbrev q := CochainComplex.toKInjectiveResolution.{g} (ℕᵒᵖ ⥤ A)

@[reducible] private noncomputable def delta : F ⋙ P ⋙ DerivedCategory.Q ⟶
    F ⋙ L ⋙ DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory.{w} A) (1 : ℤ) where
  app X := DerivedCategory.triangleOfSESδ (hS (F.obj X))
  naturality X Y f := by
    exact (DerivedCategory.triangleOfSESδ_naturality (hS (F.obj X))
      (hS (F.obj Y)) (Smap (F.map f))).symm

omit [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A] [HasDerivedCategory.{w} A]
  [HasCountableProducts (DerivedCategory.{w} A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] in
private lemma q_quasiIso (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : QuasiIso (q.app X) :=
  (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{g} (ℕᵒᵖ ⥤ A) X).2

@[reducible] private noncomputable def aIso
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) :
    F ⋙ L ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF := by
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso ((Functor.whiskerLeft F η).app X) :=
    hI _ inferInstance
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      IsIso ((Functor.whiskerRight q DerivedCategory.Q).app X) := by
    have := q_quasiIso X
    change IsIso (DerivedCategory.Q.map (q.app X))
    infer_instance
  have : IsIso (Functor.whiskerLeft F η) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight (q (A := A)) DerivedCategory.Q) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft F η) ≪≫
    (Functor.associator F DerivedCategory.Q RF).symm ≪≫
    Functor.isoWhiskerRight (asIso (Functor.whiskerRight q DerivedCategory.Q)).symm RF

@[reducible] private noncomputable def bIso
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) :
    F ⋙ P ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ E ⋙ DP := by
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso ((Functor.whiskerLeft F pc).app X) :=
    pc_isIso (F.obj X)
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      IsIso ((Functor.whiskerRight q evQ).app X) := by
    have := q_quasiIso X
    have : ∀ n : ℕᵒᵖ, IsIso ((evQ.map (q.app X)).app n) := by
      intro n
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (q.app X)))
      infer_instance
    change IsIso (evQ.map (q.app X))
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerLeft (F (A := A)) pc) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight (q (A := A)) evQ) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft F pc) ≪≫
    (Functor.associator F evQ DP).symm ≪≫
    Functor.isoWhiskerRight
      ((asIso (Functor.whiskerRight q evQ)).symm ≪≫ ε.symm) DP ≪≫
    Functor.associator DerivedCategory.Q E DP

@[reducible] private noncomputable def pPre
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) :
    DerivedCategory.Q ⋙ RF ⟶ DerivedCategory.Q ⋙ E ⋙ DP :=
  (aIso RF η hI).inv ≫ Functor.whiskerLeft F (Functor.whiskerRight inc DerivedCategory.Q) ≫
    (bIso E ε).hom

@[reducible] private noncomputable def deltaPre
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) :
    DerivedCategory.Q ⋙ E ⋙ DP ⟶
      DerivedCategory.Q ⋙ RF ⋙ shiftFunctor (DerivedCategory.{w} A) (1 : ℤ) :=
  (bIso E ε).inv ≫ delta ≫
    Functor.whiskerRight (aIso RF η hI).hom (shiftFunctor _ (1 : ℤ))

@[reducible] private noncomputable def pNat
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) : RF ⟶ E ⋙ DP :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))
      (DerivedCategory.{w} A)).preimage (pPre RF η hI E ε)

@[reducible] private noncomputable def deltaNat
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) :
    E ⋙ DP ⟶ RF ⋙ shiftFunctor (DerivedCategory.{w} A) (1 : ℤ) :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))
      (DerivedCategory.{w} A)).preimage (deltaPre RF η hI E ε)

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma bIso_diff
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.map (diff.app (F.obj X)) ≫ (bIso E ε).hom.app X =
      (bIso E ε).hom.app X ≫ dDP.app (E.obj (DerivedCategory.Q.obj X)) := by
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      IsIso ((Functor.whiskerRight q evQ).app X) := by
    have := q_quasiIso X
    have : ∀ n : ℕᵒᵖ, IsIso ((evQ.map (q.app X)).app n) := by
      intro n
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (q.app X)))
      infer_instance
    change IsIso (evQ.map (q.app X))
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight (q (A := A)) evQ) := NatIso.isIso_of_isIso_app _
  let c := (asIso (Functor.whiskerRight (q (A := A)) evQ)).symm ≪≫ ε.symm
  have hc : (bIso E ε).hom.app X = pc.app (F.obj X) ≫ DP.map (c.hom.app X) := by
    simp only [bIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, asIso_hom,
      Functor.associator, Category.id_comp, Category.comp_id, c]
  rw [hc, ← Category.assoc, pc_diff, Category.assoc]
  simpa only [Functor.comp_obj, Category.assoc] using
    congrArg (fun f ↦ pc.app (F.obj X) ≫ f)
      (dDP.naturality (c.hom.app X)).symm

private lemma pNat_app
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (pNat RF η hI E ε).app (DerivedCategory.Q.obj X) =
      (pPre RF η hI E ε).app X := by
  exact congrArg (fun t ↦ t.app X)
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))
        (DerivedCategory.{w} A)).map_preimage (pPre RF η hI E ε))

private lemma deltaNat_app
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (deltaNat RF η hI E ε).app (DerivedCategory.Q.obj X) =
      (deltaPre RF η hI E ε).app X := by
  exact congrArg (fun t ↦ t.app X)
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))
        (DerivedCategory.{w} A)).map_preimage (deltaPre RF η hI E ε))

private lemma roos_Q
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CategoryTheory.IsDerivedLimitTriangle
      (fun n : ℕ ↦ (E.obj (DerivedCategory.Q.obj X)).map (homOfLE (Nat.le_succ n)).op)
      (RF.obj (DerivedCategory.Q.obj X))
      ((pNat RF η hI E ε).app (DerivedCategory.Q.obj X))
      ((deltaNat RF η hI E ε).app (DerivedCategory.Q.obj X)) := by
  let T := DerivedCategory.triangleOfSES (hS (F.obj X))
  let U := Triangle.mk ((pNat RF η hI E ε).app (DerivedCategory.Q.obj X))
    (dDP.app (E.obj (DerivedCategory.Q.obj X)))
    ((deltaNat RF η hI E ε).app (DerivedCategory.Q.obj X))
  let a := (aIso RF η hI).app X
  let b := (bIso E ε).app X
  have e : T ≅ U := by
    refine Triangle.isoMk _ _ a b b ?_ ?_ ?_
    · change DerivedCategory.Q.map (inc.app (F.obj X)) ≫ b.hom =
        a.hom ≫ (pNat RF η hI E ε).app (DerivedCategory.Q.obj X)
      rw [pNat_app]
      simp [pPre, a, b, Category.assoc]
    · exact bIso_diff E ε X
    · change DerivedCategory.triangleOfSESδ (hS (F.obj X)) ≫
        a.hom⟦(1 : ℤ)⟧' = b.hom ≫
          (deltaNat RF η hI E ε).app (DerivedCategory.Q.obj X)
      rw [deltaNat_app]
      change DerivedCategory.triangleOfSESδ (hS (F.obj X)) ≫
        a.hom⟦(1 : ℤ)⟧' = b.hom ≫
          (b.inv ≫ DerivedCategory.triangleOfSESδ (hS (F.obj X)) ≫
            a.hom⟦(1 : ℤ)⟧')
      simp only [Iso.hom_inv_id_assoc]
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished (hS (F.obj X))) _ e.symm

private lemma natural_roos
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) :
    ∃ (p : ∀ Z, RF.obj Z ⟶ ∏ᶜ (fun n : ℕ ↦ (E.obj Z).obj (op n)))
      (δ : ∀ Z, (∏ᶜ (fun n : ℕ ↦ (E.obj Z).obj (op n))) ⟶
        (RF.obj Z)⟦(1 : ℤ)⟧),
      (∀ Z, CategoryTheory.IsDerivedLimitTriangle
        (fun n : ℕ ↦ (E.obj Z).map (homOfLE (Nat.le_succ n)).op)
        (RF.obj Z) (p Z) (δ Z)) ∧
      (∀ {Z W} (v : Z ⟶ W), RF.map v ≫ p W = p Z ≫
        Limits.Pi.map (fun n : ℕ ↦ (E.map v).app (op n))) ∧
      (∀ {Z W} (v : Z ⟶ W), Limits.Pi.map (fun n : ℕ ↦ (E.map v).app (op n)) ≫
        δ W = δ Z ≫ (RF.map v)⟦(1 : ℤ)⟧') := by
  let p := pNat RF η hI E ε
  let δ := deltaNat RF η hI E ε
  refine ⟨p.app, δ.app, ?_, fun v ↦ p.naturality v, fun v ↦ δ.naturality v⟩
  intro Z
  let X := DerivedCategory.Q.objPreimage Z
  let e : DerivedCategory.Q.obj X ≅ Z := DerivedCategory.Q.objObjPreimageIso Z
  let T := Triangle.mk (p.app (DerivedCategory.Q.obj X))
    (dDP.app (E.obj (DerivedCategory.Q.obj X))) (δ.app (DerivedCategory.Q.obj X))
  let U := Triangle.mk (p.app Z) (dDP.app (E.obj Z)) (δ.app Z)
  have h : T ∈ distTriang _ := roos_Q RF η hI E ε X
  let a := RF.mapIso e
  let b := (E ⋙ DP).mapIso e
  have f : T ≅ U := Triangle.isoMk _ _ a b b
    (p.naturality e.hom).symm (dDP.naturality (E.map e.hom)).symm
    (δ.naturality e.hom).symm
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _ h _ f.symm

end CoreWork

/-- Total derived inverse limit with independent site object, site morphism and
coefficient universes, computed on K-injective towers with the natural Roos triangle.

The site is essentially small in the coefficient universe `r`. The sheafification
and locally bijective instances provide Mathlib's abelian structure; they are canonical
on such a small site. In particular, for a pro-etale site use `uC = t + 1`, `vC = t`
and `r = max u (t + 1)` for coefficient-field universe `u`. These sizes stay independent.
This is the same statement as `ringedStrictTowerHomotopyLimit`, with all its conclusions.

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941; More on Algebra,
Tag 0H9L (auxiliary; not a blueprint node).

The coefficient sheaf is represented in `RingCat` with sectionwise commutativity `_hcomm`,
which is precisely a sheaf of commutative rings after forgetting to rings.
The index `n : ℕ` corresponds to the paper's positive index `n + 1`. The auxiliary
functor `E` evaluates a derived strict tower, with `ε` identifying its restriction to
complexes with termwise evaluation followed by localization. Thus it preserves all the
transition maps, not just the objects. The maps `p` and `δ` give Roos triangles natural
on the derived tower category. No exactness of countable products is a hypothesis.

Proof plan:
1. Replace C by its small model in `r`, using the
   equivalence of sites and module sheaves. This preserves strict towers, limits,
   quasi-isomorphisms and the derived localization. Identify strict module towers
   with modules over the constant ring sheaf on the small tower site C × ℕ. Apply
   prop-pur-kinjective-resolutions-exist to resolve every tower complex. By
   lem-weil-tower-category-levelwise-abelian, evaluation and exactness are
   levelwise. Inverse limit is right adjoint to the exact constant tower functor; it is
   additive, preserves homotopies, shifts and cones. Apply
   lem-weil-pbc-kinjective-total-derived and lem-pc-right-derived-functor-triangulated.
   The unit η is invertible on every K-injective representative by
   lem-weil-pbc-kinjective-hom-derived, giving the asserted computation.
2. Evaluation preserves K-injectives by lem-weil-tower-evaluation-kinjective. Products of
   these representatives represent derived products by lem-pc-ringed-space-product-kinjective.
   Every transition of an injective tower splits: extend the map from the finite prefix
   tower T_n(J_n) to J across its monic inclusion in T_(n+1)(J_n), using
   def-sp-injective-resolutions. With sections σ_n, solve y_n - q_n y_(n+1) = x_n by
   y_0 = 0 and y_(n+1) = σ_n(y_n - x_n). Its kernel is the inverse limit, giving the
   short exact sequence 0 → lim I → product I → product I → 0.
   Apply lem-weil-pbc-complex-ses-triangle to obtain the Roos triangle.
3. Functorial tower resolutions give commuting maps between these short exact sequences.
   Their triangles are natural, including the connecting morphism. Homotopy invariance
   and lem-weil-pbc-kinjective-hom-derived extend naturality to the derived category.
4. For a pro-zero evaluated tower and its shift s, choose r_n with pr_n s^r_n = 0.
   The finite coordinate sums pr_n t = sum_(k < r_n) pr_n s^k define a two-sided inverse
   to 1-s, by telescoping. An identity transition can be zero only at a zero object,
   when r_n = 1 suffices. The Roos triangle, its backward rotation and
   lem-weil-pbc-hom-into-triangle-exact imply id_(Rlim X) = 0, hence Rlim X is zero.
5. A strict chain map has its mapping cone in the tower category, with cones evaluated
   levelwise. Exactness sends its cone triangle to a distinguished triangle. A pro-zero
   cone tower has zero derived limit by step 4, so its first arrow is invertible by
   lem-weil-pbc-hom-into-triangle-exact and rotation (def-weil-triangulated-category). -/
theorem ringedStrictTowerHomotopyLimitIndependentCoefficients
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J RingCat.{r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{r, r, vC, uC} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R)] :
    ∃ (RF : DerivedCategory.{w}
        (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{r, r, vC, uC} R))
      (η : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ⥤
        ringedSiteModules.{r, r, vC, uC} R).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF),
      RF.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso
          (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) (ComplexShape.up ℤ)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ℤ),
        ∃ (I : CochainComplex
          (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ℤ) (j : X ⟶ I),
          I.IsKInjective ∧ QuasiIso j) ∧
      ∃ (_hshift : RF.CommShift ℤ)
        (_hproducts : HasCountableProducts
          (DerivedCategory.{w} (ringedSiteModules.{r, r, vC, uC} R)))
        (E : DerivedCategory.{w}
          (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ⥤
            (ℕᵒᵖ ⥤ DerivedCategory.{w}
              (ringedSiteModules.{r, r, vC, uC} R)))
        (_ε : DerivedCategory.Q.{w} ⋙ E ≅
          HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
            (Functor.whiskeringRight ℕᵒᵖ
              (CochainComplex (ringedSiteModules.{r, r, vC, uC} R) ℤ)
              (DerivedCategory.{w}
                (ringedSiteModules.{r, r, vC, uC} R))).obj
                  DerivedCategory.Q.{w})
        (p : ∀ Z,
          RF.obj Z ⟶ ∏ᶜ (fun n : ℕ ↦ (E.obj Z).obj (op n)))
        (δ : ∀ Z,
          (∏ᶜ (fun n : ℕ ↦ (E.obj Z).obj (op n))) ⟶ (RF.obj Z)⟦(1 : ℤ)⟧),
        RF.IsTriangulated ∧
        (∀ Z,
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ (E.obj Z).map (homOfLE (Nat.le_succ n)).op)
            (RF.obj Z) (p Z) (δ Z)) ∧
        (∀ {Z W} (v : Z ⟶ W),
          RF.map v ≫ p W = p Z ≫ Limits.Pi.map (fun n : ℕ ↦ (E.map v).app (op n))) ∧
        (∀ {Z W} (v : Z ⟶ W),
          Limits.Pi.map (fun n : ℕ ↦ (E.map v).app (op n)) ≫ δ W =
            δ Z ≫ (RF.map v)⟦(1 : ℤ)⟧') ∧
        (∀ Z,
          (∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), (E.obj Z).map (homOfLE h).op = 0) →
            IsZero (RF.obj Z)) ∧
        (∀ (X Y : CochainComplex
          (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ℤ) (v : X ⟶ Y),
          (∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
            (E.obj (DerivedCategory.Q.{w}.obj (CochainComplex.mappingCone v))).map
              (homOfLE h).op = 0) → IsIso (RF.map (DerivedCategory.Q.{w}.map v)))  := by
  let : IsGrothendieckAbelian.{r} (ringedSiteModules.{r, r, vC, uC} R) :=
    moduleSheaves_grothendieck J R
  let : IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) :=
    tower_grothendieck _
  have hres (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ℤ) :
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ℤ)
        (j : X ⟶ I), I.IsKInjective ∧ QuasiIso j := by
    obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
    exact ⟨I, j, hI, hj⟩
  let : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ⥤
      ringedSiteModules.{r, r, vC, uC} R).Additive := by
    constructor
    intro X Y f g
    apply limit.hom_ext
    intro n
    simp only [lim_map, limMap_π, Preadditive.add_comp, NatTrans.app_add,
      Preadditive.comp_add]
  obtain ⟨RF, η, hRF, hI, hshift, hTri⟩ := totalDerivedData
    (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ⥤
      ringedSiteModules.{r, r, vC, uC} R)
  let hproducts : HasCountableProducts
      (DerivedCategory.{w} (ringedSiteModules.{r, r, vC, uC} R)) :=
    derivedCountableProducts
  obtain ⟨E, ⟨ε⟩⟩ := evaluationData (A := ringedSiteModules.{r, r, vC, uC} R)
  obtain ⟨p, δ, hroos, hpn, hδn⟩ :=
    CoreWork.natural_roos RF η hI E ε
  let := hshift
  let := hTri
  have hz (Z) (h : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (E.obj Z).map (homOfLE h).op = 0) : IsZero (RF.obj Z) := by
    exact Triangle.isZero₁_of_isIso₂ _ (hroos Z) (proZero_transition_iso (E.obj Z) h)
  refine ⟨RF, η, hRF, hI, hres,
    ⟨hshift, hproducts, E, ε, p, δ, hTri, hroos, hpn, hδn, hz, ?_⟩⟩
  intro X Y v hv
  have hc := RF.map_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished v)
  exact (Triangle.isZero₃_iff_isIso₁ _ hc).mp (hz _ hv)

end CategoryTheory
