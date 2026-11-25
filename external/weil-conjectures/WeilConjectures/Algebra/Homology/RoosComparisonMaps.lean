/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A chain map of towers induces the kernel and signed-cone comparison maps,
with explicit components. No homotopy or reverse map is required.

Proof: Put U_p = eP_p.hom ≫ Pi.map(u_p) ≫ ePJ_p.inv. Product projections,
hP, hPJ and the chain-map equation for u give d_P U = U d_PJ. Naturality
of each u_p with respect to n+1 → n gives s U = U sJ, using
towerTransitionEndomorphism_natural_backward. Therefore iota_p U_p kills
sJ_p. Lift it through the limiting kernel fork hLJ_p to obtain lU_p. These
components commute with differentials: compose both sides with iJ_q, use
the chain-map equations for iota and iJ and for U, and use that iJ_q is mono.
For each p define cU_(p+1) by eC_p.hom ≫ biprod.map(U_p,U_(p+1)) ≫ eCJ_p.inv.
Every integer degree is uniquely p+1. The signed cone differential equation
for cU reduces, after the two biproduct projections, to the differential and
transition commutation equations for U; the other differentials vanish by
complex shape. Finally compare eta cU and lU etaJ after eCJ_p.hom: both have
first component zero and second component iota_(p+1) U_(p+1). This proves
the square and the two displayed component formulas. The kernel universal
property and the cone isomorphisms also determine these maps uniquely.

Source: the explicit naturality extension in the docstring of
roos_comparison_homotopy_retract (lem-weil-derived-limit-roos-complex);
Stacks Project, Derived Categories, Tag 070M provides the underlying Roos setup.
(blueprint: lem-weil-roos-comparison-maps). -/
theorem roos_comparison_maps
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A]
    (I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (u : I ⟶ J)
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
    (eta : L ⟶ C)
    (hEta : ∀ p : ℤ, eta.f (p + 1) ≫ (eC p).hom =
      biprod.lift 0 (iota.f (p + 1)))
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
    (etaJ : LJ ⟶ CJ)
    (hEtaJ : ∀ p : ℤ, etaJ.f (p + 1) ≫ (eCJ p).hom =
      biprod.lift 0 (iJ.f (p + 1)))
    : ∃ (lU : L ⟶ LJ) (cU : C ⟶ CJ),
      lU ≫ etaJ = eta ≫ cU ∧
      (∀ p : ℤ, lU.f p ≫ iJ.f p = iota.f p ≫ (eP p).hom ≫
        Limits.Pi.map (fun n ↦ (u.f p).app (Opposite.op n)) ≫ (ePJ p).inv) ∧
      (∀ p : ℤ, cU.f (p + 1) ≫ (eCJ p).hom = (eC p).hom ≫ biprod.map
        ((eP p).hom ≫ Limits.Pi.map (fun n ↦ (u.f p).app (Opposite.op n)) ≫
          (ePJ p).inv)
        ((eP (p + 1)).hom ≫
          Limits.Pi.map (fun n ↦ (u.f (p + 1)).app (Opposite.op n)) ≫
          (ePJ (p + 1)).inv)) := by
  -- The universal property is needed only for the target kernel.
  have _ := hL
  let U : ∀ p : ℤ, P.X p ⟶ PJ.X p := fun p ↦
    (eP p).hom ≫ Limits.Pi.map (fun n ↦ (u.f p).app (Opposite.op n)) ≫ (ePJ p).inv
  have hU (p q : ℤ) : U p ≫ PJ.d p q = P.d p q ≫ U q := by
    apply (cancel_mono (ePJ q).hom).1
    dsimp [U]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hPJ]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc (P.d p q), hP]
    simp only [Category.assoc, Limits.Pi.map_comp_map]
    congr 1
    congr 1
    funext n
    exact congrArg (fun f ↦ f.app (Opposite.op n)) (u.comm p q)
  have hUS (p : ℤ) : U p ≫ sJ.f p = oneSubS.f p ≫ U p := by
    have hn := towerTransitionEndomorphism_natural_backward
      (fun n ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op)
      (fun n ↦ (J.X p).map (homOfLE (Nat.le_succ n)).op)
      (fun n ↦ (u.f p).app (Opposite.op n))
      (fun n ↦ ((u.f p).naturality (homOfLE (Nat.le_succ n)).op).symm)
    dsimp [U]
    rw [hSJ, hS]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ (eP p).hom ≫ f ≫ (ePJ p).inv) hn
  have hzero (p : ℤ) : (iota.f p ≫ U p) ≫ sJ.f p = 0 := by
    rw [Category.assoc, hUS, ← Category.assoc, hKernel, zero_comp]
  let l (p : ℤ) : L.X p ⟶ LJ.X p :=
    (KernelFork.IsLimit.lift' (hLJ p) (iota.f p ≫ U p) (hzero p)).1
  have hl (p : ℤ) : l p ≫ iJ.f p = iota.f p ≫ U p :=
    (KernelFork.IsLimit.lift' (hLJ p) (iota.f p ≫ U p) (hzero p)).2
  let lU : L ⟶ LJ :=
    { f := l
      comm' := by
        intro p q _
        have : Mono (iJ.f q) := Fork.IsLimit.mono (hLJ q)
        apply (cancel_mono (iJ.f q)).1
        rw [Category.assoc, ← iJ.comm p q, ← Category.assoc, hl,
          Category.assoc, hU, ← Category.assoc, iota.comm p q,
          Category.assoc, ← hl, ← Category.assoc] }
  let c (p : ℤ) : C.X p ⟶ CJ.X p :=
    eqToHom (by congr 1; omega : C.X p = C.X (p - 1 + 1)) ≫
      (eC (p - 1)).hom ≫ biprod.map (U (p - 1)) (U (p - 1 + 1)) ≫
      (eCJ (p - 1)).inv ≫ eqToHom (by congr 1; omega)
  have hc (p : ℤ) : c (p + 1) ≫ (eCJ p).hom =
      (eC p).hom ≫ biprod.map (U p) (U (p + 1)) := by
    have transport (q : ℤ) (h : q = p)
        (h₁ : C.X (p + 1) = C.X (q + 1))
        (h₂ : CJ.X (q + 1) = CJ.X (p + 1)) :
        (eqToHom h₁ ≫ (eC q).hom ≫ biprod.map (U q) (U (q + 1)) ≫
          (eCJ q).inv ≫ eqToHom h₂) ≫ (eCJ p).hom =
            (eC p).hom ≫ biprod.map (U p) (U (p + 1)) := by
      subst q
      simp
    exact transport (p + 1 - 1) (by omega) _ _
  have hcomm (p : ℤ) : c (p + 1) ≫ CJ.d (p + 1) (p + 1 + 1) =
      C.d (p + 1) (p + 1 + 1) ≫ c (p + 1 + 1) := by
    apply (cancel_mono (eCJ (p + 1)).hom).1
    rw [Category.assoc, hCJ, ← Category.assoc, hc]
    simp only [Category.assoc]
    rw [hc, ← Category.assoc (C.d (p + 1) (p + 1 + 1)), hC]
    simp only [Category.assoc]
    congr 1
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, Preadditive.comp_sub,
        Preadditive.comp_neg, Preadditive.sub_comp, Preadditive.neg_comp,
        biprod.map_fst_assoc, biprod.map_snd_assoc, biprod.map_fst,
        biprod.lift_fst_assoc]
      rw [hU, hUS]
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd_assoc,
        biprod.map_snd, biprod.lift_snd_assoc]
      rw [hU]
  let cU : C ⟶ CJ := CochainComplex.ofHom c (fun p ↦ by
    obtain ⟨q, rfl⟩ : ∃ q : ℤ, p = q + 1 := ⟨p - 1, by omega⟩
    exact hcomm q)
  refine ⟨lU, cU, ?_, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro p
    obtain ⟨q, rfl⟩ : ∃ q : ℤ, p = q + 1 := ⟨p - 1, by omega⟩
    change l (q + 1) ≫ etaJ.f (q + 1) = eta.f (q + 1) ≫ c (q + 1)
    apply (cancel_mono (eCJ q).hom).1
    rw [Category.assoc, hEtaJ, Category.assoc, hc, ← Category.assoc, hEta]
    apply biprod.hom_ext
    · simp
    · simpa only [Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc] using hl (q + 1)
  · intro p
    exact hl p
  · intro p
    exact hc p

end CategoryTheory
