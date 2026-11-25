/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelQuotientAdicBound
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelQuotientInclusionBound

/-! # Quotient coherent formal kernels after enlarging the bound
Source: Stacks Project, Lemma 087X, claims (b)--(c).
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Quotient coherent formal-module system associated to stabilized kernel images.

Source: Stacks Project, Lemma 087X, claim (c) and the eventual kernel calculation,
under the stabilized-image equality supplied by claims (a)--(b).
The bound is enlarged to satisfy the Artin--Rees condition for the kernel in the source.
Proof: enlarge c to an eventual adicness bound. Construct
K from the explicit shifted quotient system and its proved adicness, and construct its
map to F by cokernel descent. Identity level isomorphisms give the transition and map
compatibility equations. Monicity of j and cokernel descent prove kernel vanishing.
(blueprint: lem-weil-pbc-formal-kernel-quotient-aux).
-/
theorem coherentFormalModule_kernel_quotient_aux {X : Scheme.{u}} [IsNoetherian X]
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
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) :
    ∃ d : ℕ, c ≤ d ∧ ∃ (K : CoherentFormalModule X I) (ι : K ⟶ F)
      (e : ∀ n : ℕ, formalModuleQuotient I (n + 1) (S.obj (op (n + d))) ≅
        K.obj.obj (op n)),
      (∀ n : ℕ,
        formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + d))) ≫
            (e (n + 1)).hom ≫ K.obj.map (homOfLE (Nat.le_succ n)).op =
          S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) d)).op ≫
            formalModuleQuotientπ I (n + 1) (S.obj (op (n + d))) ≫ (e n).hom) ∧
      (∀ n : ℕ,
        formalModuleQuotientπ I (n + 1) (S.obj (op (n + d))) ≫
            (e n).hom ≫ ι.hom.app (op n) =
          j.app (op (n + d)) ≫ F.obj.map (homOfLE (Nat.le_add_right n d)).op) ∧
      (∀ n : ℕ, kernel.ι (ι.hom.app (op (n + d))) ≫
        K.obj.map (homOfLE (Nat.le_add_right n d)).op = 0) := by
  obtain ⟨a, ha⟩ := coherentFormalModule_kernel_quotient_adic_bound I F H α c S j hc hS
  let d := max c a
  have hca : max c a ≤ d := by dsimp [d]; omega
  let K : CoherentFormalModule X I := ⟨formalShiftedQuotient I S d, ha d hca⟩
  let ι : K ⟶ F := ObjectProperty.homMk (formalShiftedQuotientι I F S j d)
  refine ⟨d, by dsimp [d]; omega, K, ι, fun n ↦ Iso.refl _, ?_, ?_, ?_⟩
  · intro n
    change formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + d))) ≫ 𝟙 _ ≫
        formalModuleQuotientMap I
          (S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) d)).op)
          (Nat.succ_le_succ (Nat.le_succ n)) = _
    simp [formalModuleQuotientπ, formalModuleQuotientMap]
  · intro n
    simpa only [ι, ObjectProperty.homMk, Iso.refl_hom, Category.id_comp] using
      formalShiftedQuotientι_comp I F S j d n
  · have hj (m : ℕ) : Mono (j.app (op m)) := by
      obtain ⟨a, ha⟩ := hS m
      rw [← ha]
      infer_instance
    exact coherentFormalModule_kernel_quotient_inclusion_bound I F S j hj d

end AlgebraicGeometry
