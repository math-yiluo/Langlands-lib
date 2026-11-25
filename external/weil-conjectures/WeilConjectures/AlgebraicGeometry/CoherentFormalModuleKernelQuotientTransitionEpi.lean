/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleShiftedQuotient

/-! # Surjective shifted kernel quotient transitions

Source: Stacks Project, Lemma 087X, proof of claims (a)--(c).
(blueprint: lem-weil-pbc-formal-kernel-quotient-transition-epi).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Shifted quotient transitions of the stabilized kernel image system are epimorphisms.

Source: Stacks Project, Lemma 087X, proof of claims (a)--(c).
(blueprint: lem-weil-pbc-formal-kernel-quotient-transition-epi).

Proof: Fix adjacent levels a+1 and a of S, and choose l >= a+1+c.
The map ker(alpha_l) to F_a factors through its map to F_(a+1).
By hc its images at these two levels are exactly the subobjects represented by
j_(a+1) and j_a. By hS both inclusions are monomorphisms. Naturality of j then
identifies the induced map between these images with the S transition.
The image of the composite ker(alpha_l) to S_(a+1) to S_a is all of S_a,
so the S transition is epi. Composing it with the target quotient projection remains epi.
The defining equation for formalModuleQuotientMap factors this composite through the
source quotient projection, so the induced shifted quotient transition is epi too.
This argument does not require a bound on d, and also applies to zero modules,
zero or unit ideals, and the empty scheme. -/
theorem coherentFormalModule_kernel_quotient_transition_epi {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) (d n : ℕ) :
    Epi ((formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op) := by
  have hj (a : ℕ) : Mono (j.app (op a)) := by
    obtain ⟨e, he⟩ := hS a
    rw [← he]
    infer_instance
  have htrans (a : ℕ) : Epi (S.map (homOfLE (Nat.le_succ a)).op) := by
    have := hj a
    have := hj (a + 1)
    let l := a + 1 + c
    let p := kernel.ι (α.hom.app (op l)) ≫
      F.obj.map (homOfLE (Nat.le_add_right (a + 1) c)).op
    let q := kernel.ι (α.hom.app (op l)) ≫
      F.obj.map (homOfLE (show a ≤ l by dsimp [l]; omega)).op
    obtain ⟨e, he⟩ := hS (a + 1)
    let v := Abelian.factorThruImage p ≫ e.inv
    have hv : v ≫ j.app (op (a + 1)) = p := by
      rw [← he]
      simp only [v, Category.assoc, Iso.inv_hom_id_assoc]
      exact Abelian.image.fac p
    obtain ⟨e₀, he₀⟩ := hS a
    have hq : Subobject.mk (Abelian.image.ι q) = Subobject.mk (j.app (op a)) := by
      calc
        _ = Subobject.mk (Abelian.image.ι
            (kernel.ι (α.hom.app (op (a + c))) ≫
              F.obj.map (homOfLE (Nat.le_add_right a c)).op)) := by
          convert hc l a (by dsimp [l]; omega) using 1
        _ = _ := (Subobject.mk_eq_mk_of_comm _ _ e₀ he₀).symm
    let e₁ := Subobject.isoOfMkEqMk (Abelian.image.ι q) (j.app (op a)) hq
    let w := Abelian.factorThruImage q ≫ e₁.hom
    have hw : w ≫ j.app (op a) = q := by
      simp only [w, Category.assoc, e₁, Subobject.isoOfMkEqMk_hom,
        Subobject.ofMkLEMk_comp]
      exact Abelian.image.fac q
    have hfac : v ≫ S.map (homOfLE (Nat.le_succ a)).op = w := by
      apply (cancel_mono (j.app (op a))).1
      rw [Category.assoc, j.naturality, ← Category.assoc, hv, hw]
      dsimp [p, q]
      rw [Category.assoc, ← F.obj.map_comp]
      congr 2
    have : Epi w := by dsimp [w]; infer_instance
    exact epi_of_epi_fac hfac
  let f := S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) d)).op
  have : Epi f := by
    have hgeneral (a b : ℕ) (h : a ≤ b) (hb : b = a + 1) :
        Epi (S.map (homOfLE h).op) := by
      subst b
      exact htrans a
    exact hgeneral (n + d) (n + 1 + d) _ (by omega)
  have : Epi (formalModuleQuotientπ I (n + 1) (S.obj (op (n + d)))) := by
    dsimp [formalModuleQuotientπ]
    infer_instance
  have hfac : formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + d))) ≫
      (formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op =
      f ≫ formalModuleQuotientπ I (n + 1) (S.obj (op (n + d))) := by
    simp only [formalShiftedQuotient, formalModuleQuotientMap, formalModuleQuotientπ,
      cokernel.π_desc]
    congr 2
  have : Epi (f ≫ formalModuleQuotientπ I (n + 1) (S.obj (op (n + d)))) :=
    inferInstance
  exact epi_of_epi_fac hfac

end AlgebraicGeometry
