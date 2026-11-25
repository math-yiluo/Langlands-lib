/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleShiftedQuotient
import WeilConjectures.AlgebraicGeometry.FormalKernelTransitionBound
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelQuotientTransitionEpi

/-! # Artin--Rees bounds for stabilized kernel quotients

Source: Stacks Project, Lemma 087X.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Sufficiently large shifts give the successive quotient comparisons.

Source: Stacks Project, Lemma 087X, claims (b)--(c).
(blueprint: lem-weil-pbc-formal-kernel-quotient-comparison-bound).

Proof: The transition epimorphism lemma proves surjectivity using stabilization of
kernel images, independently of Artin--Rees. The eventual exactness lemma supplies
one bound and, for every sufficiently large shift and every n, the zero composite
and exactness of the ideal-product inclusion followed by the quotient transition.
In an abelian category an exact pair with epimorphic second arrow presents its
target as the cokernel of the first arrow. Uniqueness of cokernels compares this
presentation with formalModuleQuotient. Its defining equation gives precisely
the requested equation with formalModuleQuotientπ.
-/
theorem coherentFormalModule_kernel_quotient_comparison_bound {X : Scheme.{u}} [IsNoetherian X]
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
    ∃ b : ℕ, ∀ d : ℕ, max c b ≤ d →
      ∀ n : ℕ, ∃ e :
        formalModuleQuotient I (n + 1)
          ((formalShiftedQuotient I S d).obj (op (n + 1))) ≅
          (formalShiftedQuotient I S d).obj (op n),
        formalModuleQuotientπ I (n + 1)
            ((formalShiftedQuotient I S d).obj (op (n + 1))) ≫ e.hom =
          (formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op := by
  obtain ⟨b, hb⟩ :=
    coherentFormalModule_kernel_quotient_transition_exact_bound I F H α c S j hc hS
  refine ⟨b, ?_⟩
  intro d hd n
  obtain ⟨hz, hex⟩ := hb d hd n
  have := coherentFormalModule_kernel_quotient_transition_epi I F H α c S j hc hS d n
  let k := Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
    ((formalShiftedQuotient I S d).obj (op (n + 1)))
  let t := (formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op
  let hcolim : IsColimit (CokernelCofork.ofπ t hz) := hex.gIsCokernel
  refine ⟨(cokernelIsCokernel k).coconePointUniqueUpToIso hcolim, ?_⟩
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel k) hcolim WalkingParallelPair.one

end AlgebraicGeometry
