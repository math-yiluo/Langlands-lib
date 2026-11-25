/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleShiftedQuotient

/-! # Artin--Rees bounds for stabilized kernel quotients

Source: Stacks Project, Lemma 087X.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry

/-- The kernels of the descended inclusion vanish after the defining shift.

Source: Stacks Project, Lemma 087X, uniqueness in claim (d).
(blueprint: lem-weil-pbc-formal-kernel-quotient-inclusion-bound).

Proof: Since j is monic and S_(n+d) embeds in the annihilated F_(n+d), the
transition S_(n+2d) to S_(n+d) kills I^(n+d+1). Descend it to a map k from the
shifted quotient at n+d to S_(n+d). Cokernel uniqueness identifies the inclusion
at n+d with k followed by j_(n+d), and the quotient transition to level n with
k followed by the quotient projection of S_(n+d). The kernel of the inclusion
kills k, since j_(n+d) is monic, and hence kills that quotient transition.
No Artin--Rees assumption or coherence of the quotient system is needed here.
-/
theorem coherentFormalModule_kernel_quotient_inclusion_bound
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I)
    (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hj : ∀ m : ℕ, Mono (j.app (op m))) (d n : ℕ) :
    kernel.ι ((formalShiftedQuotientι I F S j d).app (op (n + d))) ≫
      (formalShiftedQuotient I S d).map (homOfLE (Nat.le_add_right n d)).op = 0 := by
  have := hj (n + d)
  let t := S.map (homOfLE (Nat.add_le_add_right (Nat.le_add_right n d) d)).op
  have ht : Scheme.idealModuleProductι
      (Scheme.idealSheafPower I.toModulesι (n + d + 1)).2
      (S.obj (op (n + d + d))) ≫ t = 0 := by
    apply (cancel_mono (j.app (op (n + d)))).1
    rw [zero_comp, Category.assoc]
    dsimp only [t]
    rw [j.naturality]
    exact shiftedQuotient_kill I F S j d (n + d)
  let k : (formalShiftedQuotient I S d).obj (op (n + d)) ⟶ S.obj (op (n + d)) :=
    cokernel.desc _ t ht
  have hπ : formalModuleQuotientπ I (n + d + 1) (S.obj (op (n + d + d))) ≫ k = t :=
    cokernel.π_desc _ _ _
  have : Epi (formalModuleQuotientπ I (n + d + 1)
      (S.obj (op (n + d + d)))) := by
    dsimp only [formalModuleQuotientπ]
    infer_instance
  have hi : (formalShiftedQuotientι I F S j d).app (op (n + d)) =
      k ≫ j.app (op (n + d)) := by
    apply (cancel_epi (formalModuleQuotientπ I (n + d + 1)
      (S.obj (op (n + d + d))))).1
    rw [formalShiftedQuotientι_comp, ← Category.assoc, hπ]
    exact (j.naturality _).symm
  have hm : (formalShiftedQuotient I S d).map (homOfLE (Nat.le_add_right n d)).op =
      k ≫ formalModuleQuotientπ I (n + 1) (S.obj (op (n + d))) := by
    apply (cancel_epi (formalModuleQuotientπ I (n + d + 1)
      (S.obj (op (n + d + d))))).1
    rw [← Category.assoc, hπ]
    dsimp only [formalShiftedQuotient]
    simp only [formalModuleQuotientπ, formalModuleQuotientMap, cokernel.π_desc]
    rfl
  have hk : kernel.ι ((formalShiftedQuotientι I F S j d).app (op (n + d))) ≫ k = 0 := by
    apply (cancel_mono (j.app (op (n + d)))).1
    rw [zero_comp, Category.assoc, ← hi, kernel.condition]
  rw [hm, ← Category.assoc, hk, zero_comp]

end AlgebraicGeometry
