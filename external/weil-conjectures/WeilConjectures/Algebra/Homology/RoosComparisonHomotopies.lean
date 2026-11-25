/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem kernel_homotopy_lift
    {A : Type u} [Category.{v} A] [Abelian A]
    (P L : CochainComplex A ℤ) (s : P ⟶ P) (iota : L ⟶ P)
    (hk : ∀ p : ℤ, iota.f p ≫ s.f p = 0)
    (hl : ∀ p : ℤ, IsLimit (KernelFork.ofι (iota.f p) (hk p)))
    (f : L ⟶ L) (H : ∀ p q : ℤ, P.X p ⟶ P.X q)
    (hz : ∀ p q : ℤ, ¬ (ComplexShape.up ℤ).Rel q p → H p q = 0)
    (hs : ∀ p q : ℤ, H p q ≫ s.f q = s.f p ≫ H p q)
    (he : ∀ p : ℤ, f.f p ≫ iota.f p =
      iota.f p ≫ (P.d p (p + 1) ≫ H (p + 1) p +
        H p (p - 1) ≫ P.d (p - 1) p + 𝟙 _)) :
    Nonempty (Homotopy f (𝟙 L)) := by
  have hm (p : ℤ) : Mono (iota.f p) := Fork.IsLimit.mono (hl p)
  let K (p q : ℤ) : L.X p ⟶ L.X q :=
    (hl q).lift (KernelFork.ofι (iota.f p ≫ H p q) (by
      rw [Category.assoc, hs, ← Category.assoc, hk, zero_comp]))
  have hK (p q : ℤ) : K p q ≫ iota.f q = iota.f p ≫ H p q := by
    exact (hl q).fac _ WalkingParallelPair.zero
  refine ⟨{ hom := K, zero := ?_, comm := ?_ }⟩
  · intro p q hpq
    apply (cancel_mono (iota.f q)).1
    rw [hK, hz p q hpq, comp_zero, zero_comp]
  · intro p
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by
        change p - 1 + 1 = p; omega)]
    apply (cancel_mono (iota.f p)).1
    simp only [HomologicalComplex.id_f, Preadditive.add_comp, Category.id_comp,
      Category.assoc, hK]
    rw [← iota.comm (p - 1) p,
      ← Category.assoc (L.d p (p + 1)), ← iota.comm,
      ← Category.assoc (K p (p - 1)), hK]
    simp only [he, Preadditive.comp_add, Category.comp_id, Category.assoc]

private theorem biprod_map_id
    {A : Type u} [Category.{v} A] [Abelian A] (X Y : A) :
    biprod.map (𝟙 X) (𝟙 Y) = 𝟙 (X ⊞ Y) := by
  apply biprod.hom_ext <;> simp

@[reassoc]
private theorem signed_map_cast
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : CochainComplex A ℤ) (H : ∀ p q : ℤ, P.X p ⟶ P.X q)
    (a b q : ℤ) (h : b + 1 = q) :
    biprod.map (-H a b) (H (a + 1) q) ≫
      biprod.map (𝟙 _) (eqToHom (congrArg P.X h.symm)) =
        biprod.map (-H a b) (H (a + 1) (b + 1)) := by
  subst q
  apply biprod.hom_ext <;> simp

@[reassoc]
private theorem cone_diag_transport
    {A : Type u} [Category.{v} A] [Abelian A]
    (P C : CochainComplex A ℤ)
    (e : ∀ p : ℤ, C.X (p + 1) ≅ P.X p ⊞ P.X (p + 1))
    (H : ∀ p q : ℤ, P.X p ⟶ P.X q) (a b b' : ℤ) (h : b + 1 = b' + 1) :
    biprod.map (-H a b) (H (a + 1) (b + 1)) ≫ (e b).inv ≫
      eqToHom (congrArg C.X h) =
        biprod.map (-H a b') (H (a + 1) (b' + 1)) ≫ (e b').inv := by
  have hb : b = b' := by omega
  subst b'
  simp

@[reassoc]
private theorem cone_d_cast
    {A : Type u} [Category.{v} A] [Abelian A]
    (P C : CochainComplex A ℤ)
    (e : ∀ p : ℤ, C.X (p + 1) ≅ P.X p ⊞ P.X (p + 1))
    (b q : ℤ) (h : b + 1 = q) :
    eqToHom (congrArg C.X h) ≫ C.d q (q + 1) ≫ (e q).hom =
      C.d (b + 1) (b + 1 + 1) ≫ (e (b + 1)).hom ≫
        biprod.map (eqToHom (congrArg P.X h))
          (eqToHom (congrArg (fun j ↦ P.X (j + 1)) h)) := by
  subst q
  simp [biprod_map_id]

@[reassoc]
private theorem hom_target_cast
    {A : Type u} [Category.{v} A]
    (X : ℤ → A) (Y : A) (H : ∀ p : ℤ, Y ⟶ X p) (p q : ℤ) (h : p = q) :
    H p ≫ eqToHom (congrArg X h) = H q := by
  subst q
  simp

private theorem hom_middle_transport
    {A : Type u} [Category.{v} A]
    (X : ℤ → A) (Y Z : A) (f : ∀ p : ℤ, Y ⟶ X p) (g : ∀ p : ℤ, X p ⟶ Z)
    (p q : ℤ) (h : p = q) : f p ≫ g p = f q ≫ g q := by
  subst q
  rfl

private theorem signed_cone_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    (P C : CochainComplex A ℤ) (s : P ⟶ P)
    (e : ∀ p : ℤ, C.X (p + 1) ≅ P.X p ⊞ P.X (p + 1))
    (hd : ∀ p : ℤ, C.d (p + 1) (p + 1 + 1) ≫ (e (p + 1)).hom =
      (e p).hom ≫ biprod.lift
        (-(biprod.fst ≫ P.d p (p + 1)) - biprod.snd ≫ s.f (p + 1))
        (biprod.snd ≫ P.d (p + 1) (p + 1 + 1)))
    (f : C ⟶ C) (F : ∀ p : ℤ, P.X p ⟶ P.X p)
    (hf : ∀ p : ℤ, f.f (p + 1) ≫ (e p).hom =
      (e p).hom ≫ biprod.map (F p) (F (p + 1)))
    (H : ∀ p q : ℤ, P.X p ⟶ P.X q)
    (hs : ∀ p q : ℤ, H p q ≫ s.f q = s.f p ≫ H p q)
    (he : ∀ p : ℤ, F p = P.d p (p + 1) ≫ H (p + 1) p +
      H p (p - 1) ≫ P.d (p - 1) p + 𝟙 _) :
    Nonempty (Homotopy f (𝟙 C)) := by
  classical
  let ePrev (q : ℤ) : C.X q ≅ P.X (q - 1) ⊞ P.X q :=
    eqToIso (congrArg C.X (sub_add_cancel q 1).symm) ≪≫ e (q - 1) ≪≫
      biprod.mapIso (Iso.refl _) (eqToIso (congrArg P.X (sub_add_cancel q 1)))
  let K (p q : ℤ) : C.X p ⟶ C.X q :=
    if h : q + 1 = p then
      eqToHom (congrArg C.X h.symm) ≫ (e q).hom ≫
        biprod.map (-H q (q - 1)) (H (q + 1) q) ≫ (ePrev q).inv
    else 0
  refine ⟨{ hom := K, zero := ?_, comm := ?_ }⟩
  · intro p q hpq
    change ¬ (q + 1 = p) at hpq
    simp only [K, dite_eq_right hpq]
  · intro j
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, p + 1 = j := ⟨j - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (p + 1) (p + 1 + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl)]
    apply (cancel_mono (e p).hom).1
    simp only [HomologicalComplex.id_f, Preadditive.add_comp, Category.id_comp]
    rw [hf]
    simp only [K, ePrev, dite_eq_left rfl, Iso.trans_inv, biprod.mapIso_inv, Iso.refl_inv,
      eqToIso.inv, eqToHom_refl, Category.id_comp, Category.assoc]
    rw [← Category.assoc (C.d (p + 1) (p + 1 + 1)), hd]
    simp only [Category.assoc]
    rw [signed_map_cast_assoc P H (p + 1) (p + 1 - 1) (p + 1)
      (sub_add_cancel (p + 1) 1),
      signed_map_cast_assoc P H p (p - 1) p (sub_add_cancel p 1)]
    rw [cone_diag_transport_assoc P C e H (p + 1) (p + 1 - 1) p
      (by omega), Iso.inv_hom_id, Category.comp_id]
    rw [cone_d_cast P C e (p - 1) p (sub_add_cancel p 1)]
    rw [← Category.assoc (C.d (p - 1 + 1) (p - 1 + 1 + 1)),
      hd (p - 1)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    apply biprod.hom_ext
    · simp only [Category.assoc, Preadditive.add_comp, biprod.map_fst,
        biprod.map_fst_assoc, biprod.lift_fst_assoc,
        Preadditive.comp_sub, Preadditive.comp_neg, Preadditive.sub_comp,
        Preadditive.neg_comp]
      simp only [biprod.map_snd_assoc]
      rw [hom_target_cast P.X (P.X (p - 1)) (fun q ↦ P.d (p - 1) q)
        (p - 1 + 1) p (sub_add_cancel p 1)]
      rw [← Category.assoc (H (p + 1) (p - 1 + 1)),
        hom_target_cast P.X (P.X (p + 1)) (fun q ↦ H (p + 1) q ≫ s.f q)
          (p - 1 + 1) p (sub_add_cancel p 1), hs]
      rw [he p]
      simp only [Preadditive.comp_add, Category.comp_id]
      abel
    · simp only [Category.assoc, Preadditive.add_comp, biprod.map_snd,
        biprod.map_snd_assoc, biprod.lift_snd_assoc]
      rw [← Category.assoc (H (p + 1) (p - 1 + 1)),
        hom_target_cast (fun q ↦ P.X (q + 1)) (P.X (p + 1))
          (fun q ↦ H (p + 1) q ≫ P.d q (q + 1))
          (p - 1 + 1) p (sub_add_cancel p 1)]
      have hh := he (p + 1)
      rw [hom_middle_transport P.X (P.X (p + 1)) (P.X (p + 1))
        (fun q ↦ H (p + 1) q) (fun q ↦ P.d q (p + 1))
        (p + 1 - 1) p (by omega)] at hh
      rw [hh]
      simp only [Preadditive.comp_add, Category.comp_id]

-- The supplied component equations suffice without the target presentation's extra hypotheses.
set_option linter.unusedVariables false in
/-- The maps induced by a homotopy retraction of towers form homotopy
retractions of the termwise kernels and signed cones. The four component
hypotheses specify induced maps, rather than arbitrary maps of these complexes.

Proof: For hr.hom p q form H_pq = eP_p.hom ≫ Pi.map((hr.hom p q).app) ≫
eP_q.inv; put zero in the degrees where q+1 ≠ p. Product projections and
the homotopy equation for hr yield U_p R_p - id = d H + H d. Each component
of hr is a natural transformation of towers, so s_p H_pq = H_pq s_q.
Consequently iota_p H_pq kills s_q and factors uniquely through iota_q by
hL_q; use this lift as the kernel homotopy component. Compose its homotopy
equation with iota_p. The factorization formulas, hlU and hlR reduce it to
the product homotopy equation; monicity of iota_p proves the equation in L.
On C in degree p+1 define the degree-minus-one component, under eC_p and
eC_(p-1), to be the diagonal map (-H_(p,p-1), H_(p+1,p)). Set all other
components zero. By hcU, hcR and Pi.map composition the composite cU cR
is the diagonal product of U R in these presentations. Multiplying the two
signed differential matrices gives the homotopy equation: the diagonal
entries are precisely U R - id, and the off-diagonal entry is
-s_(p+1) H_(p+1,p) + H_(p+1,p) s_p, which vanishes by naturality. All nonadjacent
components vanish by the cochain shape. Thus the two constructed families
satisfy the required Homotopy equations. No exactness of products, split
transition maps, or K-injectivity is used.

Source: the explicit homotopy-invariance extension in the docstring of
roos_comparison_homotopy_retract (lem-weil-derived-limit-roos-complex);
Stacks Project, Derived Categories, Tag 070M provides the underlying Roos setup.
(blueprint: lem-weil-roos-comparison-homotopies). -/
theorem roos_comparison_homotopies
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A]
    (I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (u : I ⟶ J) (r : J ⟶ I) (hr : Homotopy (u ≫ r) (𝟙 I))
    (P L C : CochainComplex A ℤ)
    (eP : ∀ p : ℤ, P.X p ≅ ∏ᶜ (fun n : ℕ ↦ (I.X p).obj (Opposite.op n)))
    (hP : ∀ p q : ℤ, P.d p q ≫ (eP q).hom =
      (eP p).hom ≫ Limits.Pi.map (fun n ↦ (I.d p q).app (Opposite.op n)))
    (oneSubS : P ⟶ P)
    (hS : ∀ p : ℤ, oneSubS.f p = (eP p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (eP p).inv)
    (iota : L ⟶ P)
    (hKernel : ∀ p : ℤ, iota.f p ≫ oneSubS.f p = 0)
    (hL : ∀ p : ℤ, IsLimit (KernelFork.ofι (iota.f p) (hKernel p)))
    (eC : ∀ p : ℤ, C.X (p + 1) ≅ P.X p ⊞ P.X (p + 1))
    (hC : ∀ p : ℤ, C.d (p + 1) (p + 1 + 1) ≫ (eC (p + 1)).hom =
      (eC p).hom ≫ biprod.lift
        (-(biprod.fst ≫ P.d p (p + 1)) - biprod.snd ≫ oneSubS.f (p + 1))
        (biprod.snd ≫ P.d (p + 1) (p + 1 + 1)))
    (PJ LJ CJ : CochainComplex A ℤ)
    (ePJ : ∀ p : ℤ, PJ.X p ≅ ∏ᶜ (fun n : ℕ ↦ (J.X p).obj (Opposite.op n)))
    (hPJ : ∀ p q : ℤ, PJ.d p q ≫ (ePJ q).hom =
      (ePJ p).hom ≫ Limits.Pi.map (fun n ↦ (J.d p q).app (Opposite.op n)))
    (sJ : PJ ⟶ PJ)
    (hSJ : ∀ p : ℤ, sJ.f p = (ePJ p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (J.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (ePJ p).inv)
    (iJ : LJ ⟶ PJ)
    (hKJ : ∀ p : ℤ, iJ.f p ≫ sJ.f p = 0)
    (hLJ : ∀ p : ℤ, IsLimit (KernelFork.ofι (iJ.f p) (hKJ p)))
    (eCJ : ∀ p : ℤ, CJ.X (p + 1) ≅ PJ.X p ⊞ PJ.X (p + 1))
    (hCJ : ∀ p : ℤ, CJ.d (p + 1) (p + 1 + 1) ≫ (eCJ (p + 1)).hom =
      (eCJ p).hom ≫ biprod.lift
        (-(biprod.fst ≫ PJ.d p (p + 1)) - biprod.snd ≫ sJ.f (p + 1))
        (biprod.snd ≫ PJ.d (p + 1) (p + 1 + 1)))
    (lU : L ⟶ LJ) (cU : C ⟶ CJ) (lR : LJ ⟶ L) (cR : CJ ⟶ C)
    (hlU : ∀ p : ℤ, lU.f p ≫ iJ.f p = iota.f p ≫ (eP p).hom ≫
      Limits.Pi.map (fun n ↦ (u.f p).app (Opposite.op n)) ≫ (ePJ p).inv)
    (hcU : ∀ p : ℤ, cU.f (p + 1) ≫ (eCJ p).hom = (eC p).hom ≫ biprod.map
      ((eP p).hom ≫ Limits.Pi.map (fun n ↦ (u.f p).app (Opposite.op n)) ≫ (ePJ p).inv)
      ((eP (p + 1)).hom ≫
        Limits.Pi.map (fun n ↦ (u.f (p + 1)).app (Opposite.op n)) ≫ (ePJ (p + 1)).inv))
    (hlR : ∀ p : ℤ, lR.f p ≫ iota.f p = iJ.f p ≫ (ePJ p).hom ≫
      Limits.Pi.map (fun n ↦ (r.f p).app (Opposite.op n)) ≫ (eP p).inv)
    (hcR : ∀ p : ℤ, cR.f (p + 1) ≫ (eC p).hom = (eCJ p).hom ≫ biprod.map
      ((ePJ p).hom ≫ Limits.Pi.map (fun n ↦ (r.f p).app (Opposite.op n)) ≫ (eP p).inv)
      ((ePJ (p + 1)).hom ≫
        Limits.Pi.map (fun n ↦ (r.f (p + 1)).app (Opposite.op n)) ≫ (eP (p + 1)).inv))
    : Nonempty (Homotopy (lU ≫ lR) (𝟙 L)) ∧
      Nonempty (Homotopy (cU ≫ cR) (𝟙 C)) := by
  let H (p q : ℤ) : P.X p ⟶ P.X q :=
    (eP p).hom ≫ Limits.Pi.map (fun n ↦ (hr.hom p q).app (Opposite.op n)) ≫
      (eP q).inv
  let F (p : ℤ) : P.X p ⟶ P.X p :=
    (eP p).hom ≫ Limits.Pi.map
      (fun n ↦ ((u ≫ r).f p).app (Opposite.op n)) ≫ (eP p).inv
  have hHz (p q : ℤ) (hpq : ¬ (ComplexShape.up ℤ).Rel q p) : H p q = 0 := by
    dsimp [H]
    rw [hr.zero p q hpq]
    have hm : Limits.Pi.map
        (fun n ↦ (0 : I.X p ⟶ I.X q).app (Opposite.op n)) = 0 := by
      apply Limits.Pi.hom_ext
      intro n
      simp
    rw [hm, zero_comp, comp_zero]
  have hHs (p q : ℤ) : H p q ≫ oneSubS.f q = oneSubS.f p ≫ H p q := by
    dsimp [H]
    rw [hS, hS]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply towerTransitionEndomorphism_natural_backward
    intro n
    exact ((hr.hom p q).naturality (homOfLE (Nat.le_succ n)).op).symm
  have hEq (p : ℤ) : F p = P.d p (p + 1) ≫ H (p + 1) p +
      H p (p - 1) ≫ P.d (p - 1) p + 𝟙 _ := by
    apply (cancel_mono (eP p).hom).1
    dsimp [F, H]
    simp only [Preadditive.add_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    rw [← Category.assoc (P.d p (p + 1)), hP]
    have hd := hP (p - 1) p
    have hd' : (eP (p - 1)).inv ≫ P.d (p - 1) p ≫ (eP p).hom =
        Limits.Pi.map (fun n ↦ (I.d (p - 1) p).app (Opposite.op n)) := by
      rw [hd, Iso.inv_hom_id_assoc]
    simp only [Category.assoc]
    rw [hd']
    apply Limits.Pi.hom_ext
    intro n
    have hh := congrArg (fun f ↦ f.app (Opposite.op n)) (hr.comm p)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by change p - 1 + 1 = p; omega)] at hh
    simpa only [Category.assoc, Limits.Pi.map_π_assoc, Limits.Pi.map_π,
      Preadditive.add_comp, Preadditive.comp_add, Category.comp_id,
      HomologicalComplex.comp_f, NatTrans.comp_app, NatTrans.app_add,
      HomologicalComplex.id_f, NatTrans.id_app] using
      congrArg (fun f ↦ (eP p).hom ≫
        Limits.Pi.π (fun n ↦ (I.X p).obj (Opposite.op n)) n ≫ f) hh
  have hKernelEq (p : ℤ) : (lU ≫ lR).f p ≫ iota.f p = iota.f p ≫ F p := by
    simp only [HomologicalComplex.comp_f, Category.assoc, hlR]
    rw [← Category.assoc (lU.f p), hlU]
    dsimp [F]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Limits.Pi.map_comp_map]
  constructor
  · exact kernel_homotopy_lift P L oneSubS iota hKernel hL (lU ≫ lR) H hHz hHs
      (fun p ↦ by rw [hKernelEq, hEq])
  · have hConeEq (p : ℤ) : (cU ≫ cR).f (p + 1) ≫ (eC p).hom =
        (eC p).hom ≫ biprod.map (F p) (F (p + 1)) := by
      simp only [HomologicalComplex.comp_f, Category.assoc, hcR]
      rw [← Category.assoc (cU.f (p + 1)), hcU]
      dsimp [F]
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc,
          Iso.inv_hom_id_assoc, ← Limits.Pi.map_comp_map]
      · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc,
          Iso.inv_hom_id_assoc, ← Limits.Pi.map_comp_map]
    exact signed_cone_homotopy P C oneSubS eC hC (cU ≫ cR) F hConeEq H hHs hEq

end CategoryTheory
