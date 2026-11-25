/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-! The derived universal property of the explicit Roos cone.
Source: Stacks Project, Cohomology on Sites, Tag 0941
(auxiliary; not a blueprint node). -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC r w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem roos_kernel
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
               exact roos_compatible F (fun n ↦ k ≫ P.proj n) ha
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

private noncomputable def roos_cone_coords
    {A : Type*} [Category* A] [Abelian A] {P : CochainComplex A ℤ}
    (t : P ⟶ P) (p : ℤ) :
    ((CochainComplex.mappingCone t)⟦(-1 : ℤ)⟧).X (p + 1) ≅ P.X p ⊞ P.X (p + 1) :=
  (CochainComplex.mappingCone t).shiftFunctorObjXIso
      (-1) (p + 1) p (by omega) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod t p (p + 1) rfl ≪≫
      biprod.braiding _ _

private theorem roos_cone_d
    {A : Type*} [Category* A] [Abelian A] (P : CochainComplex A ℤ)
    (t : P ⟶ P) (p : ℤ) :
    ((CochainComplex.mappingCone t)⟦(-1 : ℤ)⟧).d (p + 1) (p + 1 + 1) ≫
        (roos_cone_coords t (p + 1)).hom =
      (roos_cone_coords t p).hom ≫ biprod.lift
        (-(biprod.fst ≫ P.d p (p + 1)) - biprod.snd ≫ t.f (p + 1))
        (biprod.snd ≫ P.d (p + 1) (p + 1 + 1)) := by
  let C := (CochainComplex.mappingCone t)⟦(-1 : ℤ)⟧
  let eS (p : ℤ) := (CochainComplex.mappingCone t).shiftFunctorObjXIso
    (-1) (p + 1) p (by omega)
  let eB (p : ℤ) := HomologicalComplex.homotopyCofiber.XIsoBiprod t p (p + 1) rfl
  let eC (p : ℤ) : C.X (p + 1) ≅ P.X p ⊞ P.X (p + 1) :=
    eS p ≪≫ eB p ≪≫ biprod.braiding _ _
  change C.d (p + 1) (p + 1 + 1) ≫ (eC (p + 1)).hom =
    (eC p).hom ≫ biprod.lift
      (-(biprod.fst ≫ P.d p (p + 1)) - biprod.snd ≫ t.f (p + 1))
      (biprod.snd ≫ P.d (p + 1) (p + 1 + 1))
  have hd : C.d (p + 1) (p + 1 + 1) ≫ (eS (p + 1)).hom =
      -(eS p).hom ≫ (CochainComplex.mappingCone t).d p (p + 1) := by
    dsimp only [C, eS, CochainComplex.shiftFunctorObjXIso]
    simp only [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg,
      Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.neg_comp,
      HomologicalComplex.d_comp_XIsoOfEq_hom,
      HomologicalComplex.XIsoOfEq_hom_comp_d]
  dsimp only [eC, Iso.trans_hom]
  rw [← Category.assoc, hd]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.braiding_hom, biprod.lift_fst,
      Preadditive.neg_comp, Preadditive.comp_sub, Preadditive.comp_neg]
    rw [biprod.lift_fst_assoc, biprod.lift_snd_assoc]
    dsimp only [eB]
    have hd_snd := HomologicalComplex.homotopyCofiber.d_sndX t p (p + 1) rfl
    have hp (r q : ℤ) (h : (ComplexShape.up ℤ).Rel r q) :
        HomologicalComplex.homotopyCofiber.sndX t r =
          (HomologicalComplex.homotopyCofiber.XIsoBiprod t r q h).hom ≫
            biprod.snd := by
      obtain rfl := (ComplexShape.up ℤ).next_eq' h
      dsimp only [HomologicalComplex.homotopyCofiber.sndX]
      rw [dite_eq_left h]
    simp only [hp p (p + 1) rfl, hp (p + 1) (p + 1 + 1) rfl,
      HomologicalComplex.homotopyCofiber.fstX, Category.assoc] at hd_snd
    change -(eS p).hom ≫ HomologicalComplex.homotopyCofiber.d t p (p + 1) ≫ _ = _
    rw [hd_snd]
    simp only [Preadditive.comp_add]
    abel
  · simp only [Category.assoc, biprod.braiding_hom, biprod.lift_snd,
      Preadditive.neg_comp]
    rw [biprod.lift_snd_assoc]
    dsimp only [eB]
    have hd_fst := HomologicalComplex.homotopyCofiber.d_fstX t p (p + 1)
      (p + 1 + 1) rfl rfl
    dsimp only [HomologicalComplex.homotopyCofiber.fstX] at hd_fst
    simp only [Category.assoc] at hd_fst
    change -(eS p).hom ≫ HomologicalComplex.homotopyCofiber.d t p (p + 1) ≫ _ = _
    rw [hd_fst]
    simp only [Preadditive.comp_neg, neg_neg]

private theorem roos_inclusion_quasiIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasExactLimitsOfShape (Discrete ℕ) A] [EnoughInjectives A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] : QuasiIso (roosι I) := by
  classical
  let c := limit.cone I.asFunctor
  let hc := limit.isLimit I.asFunctor
  let P := Fan.mk (roosP I) (fun n : ℕ ↦ Pi.π _ n)
  let hP : IsLimit P := productIsProduct _
  let iota := Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))
  let t := roosU I
  have hiota (n : ℕ) : iota ≫ P.proj n = c.π.app (op n) := by simp [iota, P, c]
  have ht (n : ℕ) : t ≫ P.proj n = P.proj n -
      P.proj (n + 1) ≫ I.asFunctor.map (homOfLE (Nat.le_succ n)).op := by
    simp [t, P, towerTransitionEndomorphism, towerProductShift,
      Preadditive.sub_comp]
  obtain ⟨hz, ⟨hK⟩⟩ := roos_kernel I.asFunctor c hc P hP iota t hiota ht
  let ev (p : ℤ) := HomologicalComplex.eval A (ComplexShape.up ℤ) p
  let F (p : ℤ) := Fan.mk (P.pt.X p) (fun n : ℕ ↦ (P.proj n).f p)
  have hF (p : ℤ) : IsLimit (F p) :=
    (Fan.isLimitMapConeEquiv (ev p) _ P) (isLimitOfPreserves (ev p) hP)
  let eP (p : ℤ) : P.pt.X p ≅ ∏ᶜ (fun n : ℕ ↦ (I.X p).obj (Opposite.op n)) :=
    (hF p).conePointUniqueUpToIso (productIsProduct _)
  have heP (p : ℤ) (n : ℕ) : (eP p).hom ≫
      Pi.π (fun n : ℕ ↦ (I.X p).obj (Opposite.op n)) n = (P.proj n).f p :=
    (hF p).conePointUniqueUpToIso_hom_comp (productIsProduct _) ⟨n⟩
  have hdP (p q : ℤ) : P.pt.d p q ≫ (eP q).hom =
      (eP p).hom ≫ Limits.Pi.map (fun n ↦ (I.d p q).app (Opposite.op n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Limits.Pi.map_π, heP, reassoc_of% heP]
    exact ((P.proj n).comm p q).symm
  have hs (p : ℤ) : t.f p = (eP p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (eP p).inv := by
    apply (cancel_mono (eP p).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, heP]
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π, heP,
      reassoc_of% heP]
    exact congrArg (fun f ↦ f.f p) (ht n)
  have hKernel (p : ℤ) : iota.f p ≫ t.f p = 0 :=
    congrArg (fun f ↦ f.f p) hz
  have hL (p : ℤ) : IsLimit (KernelFork.ofι (iota.f p) (hKernel p)) :=
    KernelFork.mapIsLimit _ hK (ev p)
  let C := (CochainComplex.mappingCone t)⟦(-1 : ℤ)⟧
  let eS (p : ℤ) := (CochainComplex.mappingCone t).shiftFunctorObjXIso
    (-1) (p + 1) p (by omega)
  let eB (p : ℤ) := HomologicalComplex.homotopyCofiber.XIsoBiprod t p (p + 1) rfl
  let eC (p : ℤ) : C.X (p + 1) ≅ P.pt.X p ⊞ P.pt.X (p + 1) :=
    eS p ≪≫ eB p ≪≫ biprod.braiding _ _
  have hdC (p : ℤ) : C.d (p + 1) (p + 1 + 1) ≫ (eC (p + 1)).hom =
      (eC p).hom ≫ biprod.lift
        (-(biprod.fst ≫ P.pt.d p (p + 1)) - biprod.snd ≫ t.f (p + 1))
        (biprod.snd ≫ P.pt.d (p + 1) (p + 1 + 1)) := by
    exact roos_cone_d P.pt t p
  obtain ⟨eta, heta, hq, hiso⟩ := roosComplex_quasiIso A I
    P.pt c.pt C eP hdP t hs iota hKernel hL eC hdC
  have heq : eta = roosι I := by
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    apply (cancel_mono (roosχ I p).hom).1
    exact (heta p).trans (roosι_χ I p).symm
  simpa only [heq] using hq

private theorem roos_map_quasiIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [HasExactLimitsOfShape (Discrete ℕ) A]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) [hf : QuasiIso f] :
    QuasiIso (roosF.map f) := by
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans (F := Discrete.functor (fun n : ℕ ↦ X.asFunctor.obj (op n)))
        (G := Discrete.functor (fun n : ℕ ↦ Y.asFunctor.obj (op n)))
        (fun n ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
          (op n.as))).app n) :=
    (HomologicalComplex.quasiIso_iff_evaluation f).mp hf (op n.as)
  have hp : QuasiIso (roosPmap f) := HomologicalComplex.quasiIso_limMap _
  let τ := CochainComplex.mappingCone.triangleMap (roosU X) (roosU Y)
    (roosPmap f) (roosPmap f) (roosU_natural f)
  have hc : IsIso (DerivedCategory.Q.map (roosConeFunctor.map f)) :=
    CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map τ)
      (DerivedCategory.mappingCone_triangle_distinguished (roosU X))
      (DerivedCategory.mappingCone_triangle_distinguished (roosU Y))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
  have : QuasiIso (roosConeFunctor.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hc
  change QuasiIso ((roosConeFunctor.map f)⟦(-1 : ℤ)⟧')
  infer_instance

private theorem roos_universal
    {B D H : Type*} [Category* B] [Category* D] [Category* H]
    (W : MorphismProperty B) (Q : B ⥤ D) [Q.IsLocalization W]
    (G F : B ⥤ H) (CF : D ⥤ H) (κ : F ≅ Q ⋙ CF) (ν : G ⟶ F)
    (T : B ⥤ B) (q : 𝟭 B ⟶ T)
    (hq : ∀ X, W (q.app X)) (hν : ∀ X, IsIso (ν.app (T.obj X))) :
    CF.IsRightDerivedFunctor (ν ≫ κ.hom) W := by
  classical
  have : ∀ X, IsIso (Q.map (q.app X)) := fun X ↦
    Localization.inverts Q W _ (hq X)
  have hFq (X : B) : IsIso (F.map (q.app X)) := by
    have he : F.map (q.app X) = κ.hom.app X ≫
        CF.map (Q.map (q.app X)) ≫ κ.inv.app (T.obj X) := by
      have hn := κ.hom.naturality (q.app X)
      dsimp only [Functor.comp_map, Functor.id_obj] at hn
      apply (cancel_mono (κ.hom.app (T.obj X))).1
      simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
        Category.comp_id] using hn
    rw [he]
    infer_instance
  have : ∀ X, IsIso (ν.app (T.obj X)) := hν
  let lift (E : D ⥤ H) (β : G ⟶ Q ⋙ E) : F ⟶ Q ⋙ E :=
    { app := fun X ↦ F.map (q.app X) ≫ inv (ν.app (T.obj X)) ≫
        β.app (T.obj X) ≫ inv (E.map (Q.map (q.app X)))
      naturality := by
        intro X Y f
        have hqf := q.naturality f
        dsimp only [Functor.id_map] at hqf
        have := Localization.inverts Q W _ (hq X)
        have := Localization.inverts Q W _ (hq Y)
        dsimp only [Functor.comp_map]
        apply (cancel_mono (E.map (Q.map (q.app Y)))).1
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rw [← F.map_comp_assoc, hqf, F.map_comp, Category.assoc]
        apply (cancel_epi (F.map (q.app X))).2
        have hn : F.map (T.map f) ≫ inv (ν.app (T.obj Y)) =
            inv (ν.app (T.obj X)) ≫ G.map (T.map f) := by
          apply (cancel_epi (ν.app (T.obj X))).1
          rw [← Category.assoc, ← ν.naturality]
          simp
        rw [← Category.assoc, hn, Category.assoc, β.naturality]
        simp only [Functor.comp_map]
        congr 3
        rw [← E.map_comp, ← Q.map_comp, hqf, Q.map_comp, E.map_comp]
        simp }
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W H
  let desc (E : D ⥤ H) (β : G ⟶ Q ⋙ E) : CF ⟶ E :=
    ff.preimage (κ.inv ≫ lift E β)
  have hdesc (E : D ⥤ H) (β : G ⟶ Q ⋙ E) :
      Functor.whiskerLeft Q (desc E β) = κ.inv ≫ lift E β :=
    ff.map_preimage _
  have hfac (E : D ⥤ H) (β : G ⟶ Q ⋙ E) :
      (ν ≫ κ.hom) ≫ Functor.whiskerLeft Q (desc E β) = β := by
    rw [hdesc]
    ext X
    have := Localization.inverts Q W _ (hq X)
    simp only [NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
    dsimp only [lift]
    rw [← ν.naturality_assoc]
    simp only [IsIso.hom_inv_id_assoc]
    rw [β.naturality_assoc]
    simp
  have huniq (E : D ⥤ H) (a b : CF ⟶ E)
      (ha : (ν ≫ κ.hom) ≫ Functor.whiskerLeft Q a =
        (ν ≫ κ.hom) ≫ Functor.whiskerLeft Q b) : a = b := by
    apply Localization.natTrans_ext Q W
    intro X
    have h := NatTrans.congr_app ha (T.obj X)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    have ht : a.app (Q.obj (T.obj X)) = b.app (Q.obj (T.obj X)) := by
      exact (cancel_epi (ν.app (T.obj X) ≫ κ.hom.app (T.obj X))).1 h
    have := Localization.inverts Q W _ (hq X)
    apply (cancel_mono (E.map (Q.map (q.app X)))).1
    rw [← a.naturality, ← b.naturality, ht]
  constructor
  constructor
  refine ⟨IsInitial.ofUniqueHom (fun E ↦ StructuredArrow.homMk
    (desc E.right E.hom) (hfac E.right E.hom)) ?_⟩
  intro E m
  apply StructuredArrow.hom_ext
  apply huniq
  change (ν ≫ κ.hom) ≫ Functor.whiskerLeft Q m.right =
    (ν ≫ κ.hom) ≫ Functor.whiskerLeft Q (desc E.right E.hom)
  exact m.w.trans (hfac E.right E.hom).symm

private theorem roos_tower_grothendieck
    (A : Type*) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    (K : Type v) [SmallCategory K] : IsGrothendieckAbelian.{v} (K ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : K ↦ (evaluationLeftAdjoint A j).obj G) := by
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
  let : HasSeparator (K ⥤ A) :=
    ⟨_, hS.isSeparator_coproduct⟩
  let : Limits.HasFilteredColimitsOfSize.{v, v} (K ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{v, v} (K ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact {}

/-- The explicit cone model descends and its canonical limit inclusion is a total
right-derived unit. On every K-injective tower with injective terms the inclusion is
a quasi-isomorphism.

Source: Stacks Project, Cohomology on Sites, Tag 0941, lemma-derived-limit-is-ok,
with the strict-cone refinement of steps 2--5 of lem-weil-strict-roos-comparison
(auxiliary; not a blueprint node).

Proof: Exact countable products preserve quasi-isomorphisms of evaluated complexes.
The natural mapping-cone triangles and two-out-of-three show that roosF preserves
quasi-isomorphisms; localization gives CF and κ. Identify the ordinary-limit inclusion
as the kernel of 1-s using the product and limit universal properties. Transport these
properties to every degree and compute the signed cone differential. The existing
roosComplex_quasiIso theorem then proves that the explicitly constructed roosι is a
quasi-isomorphism on K-injective towers.

Module sheaves are Grothendieck abelian. In a small diagram category, evaluation left
adjoints applied to a separator form a separating family; their coproduct is a separator,
and filtered colimits are exact pointwise. Lift the tower index to the module universe
and transport along its equivalence to obtain functorial K-injective tower resolutions.
For a functor G, a natural map ν:G→F invertible on resolutions q:X→T X, and β:G→Q E,
the formula F(q) ν(T X)⁻¹ β(T X) E(Qq)⁻¹ defines a natural map F→Q E. Fully faithful
whiskering along the localization descends it to CF→E. Naturality proves its unit
factorization, and cancellation on resolutions proves uniqueness, then naturality along
Qq gives uniqueness everywhere. Apply this construction with ν=Q(roosι). Zero towers,
identity transitions and zero transitions satisfy the same kernel computation. -/
theorem strictRoosDerivation
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{w}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    : ∃ (CF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
        DerivedCategory.{w} (ringedSiteModules.{max uC vC r} R))
      (κ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF),
      CF.IsRightDerivedFunctor (roosDerivedUnit κ)
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)
          (ComplexShape.up ℤ)) ∧
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
        [I.IsKInjective] (_hIinj : ∀ p : ℤ, Injective (I.X p)), QuasiIso (roosι I) := by
  classical
  let A := ringedSiteModules.{max uC vC r} R
  let : IsGrothendieckAbelian.{max uC vC r} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{uC, vC, max uC vC r, 0} J R
  let : IsGrothendieckAbelian.{max uC vC r} (ℕᵒᵖ ⥤ A) :=
    by
      let : IsGrothendieckAbelian.{max uC vC r}
          (AsSmall.{max uC vC r} ℕᵒᵖ ⥤ A) :=
        roos_tower_grothendieck A (AsSmall.{max uC vC r} ℕᵒᵖ)
      let e : ℕᵒᵖ ≌ AsSmall.{max uC vC r} ℕᵒᵖ := AsSmall.equiv
      exact IsGrothendieckAbelian.of_equivalence (Equivalence.congrLeft e.symm)
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)
  have hinv : W.IsInvertedBy (roosF ⋙ DerivedCategory.Q.{w}) := by
    intro X Y f hf
    have : QuasiIso f := hf
    have : QuasiIso (roosF.map f) := roos_map_quasiIso f
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (roosF.map f)))
  let CF := Localization.lift (roosF ⋙ DerivedCategory.Q.{w}) hinv DerivedCategory.Q
  let κ := (Localization.fac (roosF ⋙ DerivedCategory.Q.{w}) hinv
    DerivedCategory.Q).symm
  refine ⟨CF, κ, ?_, ?_⟩
  · exact roos_universal W DerivedCategory.Q _ _ CF κ
      (Functor.whiskerRight roosInclusion DerivedCategory.Q)
      (CochainComplex.kInjectiveResolutionFunctor.{max uC vC r} (ℕᵒᵖ ⥤ A))
      (CochainComplex.toKInjectiveResolution.{max uC vC r} (ℕᵒᵖ ⥤ A))
      (fun X ↦ (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2)
      (fun X ↦ by
        have := roos_inclusion_quasiIso
          ((CochainComplex.kInjectiveResolutionFunctor.{max uC vC r} (ℕᵒᵖ ⥤ A)).obj X)
        exact inferInstanceAs (IsIso (DerivedCategory.Q.map (roosι _))))
  · intro I hI _
    exact roos_inclusion_quasiIso I

end CategoryTheory
