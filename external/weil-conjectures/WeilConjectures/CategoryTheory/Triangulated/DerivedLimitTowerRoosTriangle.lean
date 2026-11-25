/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import WeilConjectures.Algebra.Homology.RoosComplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

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

set_option backward.isDefEq.respectTransparency false in
/-- A Roos triangle with the localized product complex as its middle objects.
Source: Stacks Project, Derived Categories, Tags 0BK7 and 070M, using the
arbitrary K-injective tower extension `roosComplex_quasiIso`.

Proof: Evaluation preserves limits of complexes, so the limit cone c and the
product fan P remain limiting in each degree. The projection equations for t
identify its degree-p component with one minus the transition shift, under the
unique isomorphism from P.pt.X p to the chosen product of (I.X p). The equations
for iota identify c.pt.X p with the kernel of that component: the kernel equation
is the compatibility equation for an inverse-limit family, and its universal
property follows by lifting such a family through c. Construct the shifted
mapping cone of t, with terms P.pt.X (p-1) biproduct P.pt.X p and differential
(-d x - t y, d y). The kernel-cone comparison has components (0, iota).
Apply `roosComplex_quasiIso` with these degreewise product isomorphisms, kernel
forks and cone isomorphisms; the comparison localizes to an isomorphism. Localize
the mapping-cone triangle and rotate it backwards. Its first map, after the
comparison isomorphism and the conventional sign isomorphism of the first
object, is Q(iota), and its second map is Q(t). Transport the distinguished
triangle along these isomorphisms. Its third map supplies delta.
This step neither proves that Q(P.pt) is a derived-category product nor uses
chosen products in the derived category; the caller proves and applies that
separate fact.
(blueprint: lem-weil-derived-limit-tower-roos-triangle)
-/
theorem derivedCategory_tower_roos_triangle
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A] [EnoughInjectives A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    (c : Cone I.asFunctor) (hc : IsLimit c)
    (P : Fan (fun n : ℕ ↦ I.asFunctor.obj (Opposite.op n))) (hP : IsLimit P)
    (iota : c.pt ⟶ P.pt) (t : P.pt ⟶ P.pt)
    (hiota : ∀ n : ℕ, iota ≫ P.proj n = c.π.app (Opposite.op n))
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj n -
      P.proj (n + 1) ≫ I.asFunctor.map (homOfLE (Nat.le_succ n)).op) :
    ∃ δ : DerivedCategory.Q.obj P.pt ⟶ (DerivedCategory.Q.obj c.pt)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk (DerivedCategory.Q.map iota)
        (DerivedCategory.Q.map t) δ ∈ distTriang (DerivedCategory A) := by
  classical
  obtain ⟨hz, ⟨hK⟩⟩ := tower_kernel I.asFunctor c hc P hP iota t hiota ht
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
  obtain ⟨eta, heta, hq, hiso⟩ := roosComplex_quasiIso A I
    P.pt c.pt C eP hdP t hs iota hKernel hL eC hdC
  have hcomp : eta ≫ CochainComplex.mappingCocone.fst t = iota := by
    ext r
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective r
    have h := congrArg (fun f ↦ f ≫ biprod.snd) (heta p)
    simp only [Category.assoc, biprod.lift_snd] at h
    dsimp only [eC, Iso.trans_hom] at h
    simp only [Category.assoc, biprod.braiding_hom, biprod.lift_snd] at h
    dsimp only [eB] at h
    change eta.f (p + 1) ≫ (CochainComplex.mappingCocone.fst t).f (p + 1) = _
    have hf : (CochainComplex.mappingCocone.fst t).f (p + 1) =
        (eS p).hom ≫ HomologicalComplex.homotopyCofiber.fstX t p (p + 1) rfl := by
      simp [CochainComplex.mappingCocone.fst, CochainComplex.mappingCone.fst, eS,
        CochainComplex.shiftFunctorObjXIso,
        CochainComplex.HomComplex.Cochain.leftShift_v
          (n := 1) _ _ _ _ _ (p + 1) _ p (by omega)]
    rw [hf]
    exact h
  have : IsIso (DerivedCategory.Q.map eta) := hiso
  let Q := DerivedCategory.Q (C := A)
  let T := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle t)
  have hT : T ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.mappingCocone_triangle_distinguished t
  let delta := T.mor₃ ≫ (inv (Q.map eta))⟦(1 : ℤ)⟧'
  refine ⟨delta, ?_⟩
  apply Pretriangulated.isomorphic_distinguished T hT
  refine Pretriangulated.Triangle.isoMk _ _ (asIso (Q.map eta))
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change Q.map iota ≫ 𝟙 _ = Q.map eta ≫
      Q.map (CochainComplex.mappingCocone.fst t)
    rw [Category.comp_id, ← Q.map_comp, hcomp]
  · change Q.map t ≫ 𝟙 _ = 𝟙 _ ≫ Q.map t
    simp
  · dsimp only [Pretriangulated.Triangle.mk, Iso.refl_hom, asIso_hom]
    simp [delta]

end CategoryTheory
