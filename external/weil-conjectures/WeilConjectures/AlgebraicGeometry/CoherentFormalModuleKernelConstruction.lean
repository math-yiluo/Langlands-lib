/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffine
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelStabilized
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelQuotient
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.RingTheory.Filtration

/-! # Stabilized-image construction for a formal kernel

Source: Stacks Project, Lemma 087X, claims (a)--(c) and the Artin--Rees calculation.
(blueprint: lem-weil-pbc-formal-kernel-construction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Stabilized images yield the coherent quotient system and its inclusion. The kernels
of the inclusion components vanish after transitioning by the same uniform bound.
This statement makes no assertion about the universal factorization property.

Source: Stacks Project, Lemma 087X, claims (a)--(c), with the uniqueness calculation
expanded from its Artin--Rees bound.
(blueprint: lem-weil-pbc-formal-kernel-construction).

Proof: Choose a finite affine Noetherian cover. The affine formal-module equivalence
identifies the morphism with a map f : M → N of finite modules over the adic completion.
That ring is Noetherian. Apply Artin--Rees both to ker f in M and to im f in N; enlarge
the bounds to their maximum on the cover. With L = ker f, the second application gives
f⁻¹(I^l N) ⊆ L + I^(l-c) M. Thus the images in level m+1 equal
(L + I^(m+1) M)/I^(m+1) M whenever l ≥ m+c. Kernels and images are quasi-coherent;
the locally Noetherian coherence criterion makes these images coherent. Equality of
the affine submodules proves stabilization globally. Restrict transitions to those
images; their inclusions are monic, so the restrictions obey the functor laws and form S.
Take its shifted level-n quotient by I^(n+1). Its affine sections are
L/(L ∩ I^(n+c+1) M + I^(n+1) L), which equal L/I^(n+1) L by the first Artin--Rees
application. These are coherent and annihilated by I^(n+1); the successive quotient
comparisons identify the required reductions. The induced transitions define K.
The inclusion followed by the transition to F_n kills the ideal product and therefore
descends through the quotient, defining ι and the stated compatibility equations.
Finally ker(ι at n+c) has affine sections
(L ∩ I^(n+c+1) M)/I^(n+c+1) L. Artin--Rees places its numerator in I^(n+1) L,
so its transition into L/I^(n+1) L is zero. Zero maps are detected on the affine cover.
The same construction covers zero modules, I=0, I=O_X, and the empty scheme.
-/
theorem coherentFormalModule_kernel_construction {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I)
    (α : F ⟶ H) :
    ∃ c : ℕ,
      (∀ (l m : ℕ) (h : m + c ≤ l),
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op))) ∧
      ∃ (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj),
        (∀ m : ℕ, ∃ e : S.obj (op m) ≅
            Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
              F.obj.map (homOfLE (Nat.le_add_right m c)).op),
          e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) ∧
        ∃ (K : CoherentFormalModule X I) (ι : K ⟶ F)
          (e : ∀ n : ℕ, formalModuleQuotient I (n + 1) (S.obj (op (n + c))) ≅
            K.obj.obj (op n)),
          (∀ n : ℕ,
            formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + c))) ≫
                (e (n + 1)).hom ≫ K.obj.map (homOfLE (Nat.le_succ n)).op =
              S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) c)).op ≫
                formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫ (e n).hom) ∧
          (∀ n : ℕ,
            formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫
                (e n).hom ≫ ι.hom.app (op n) =
              j.app (op (n + c)) ≫ F.obj.map (homOfLE (Nat.le_add_right n c)).op) ∧
          (∀ n : ℕ, kernel.ι (ι.hom.app (op (n + c))) ≫
            K.obj.map (homOfLE (Nat.le_add_right n c)).op = 0) := by
  obtain ⟨c, hc, S, j, hS⟩ :=
    coherentFormalModule_kernel_stabilized_aux I F H α
  obtain ⟨d, hcd, K, ι, e, heq, hι, hker⟩ :=
    coherentFormalModule_kernel_quotient_aux I F H α c S j hc hS
  have hd (l m : ℕ) (h : m + d ≤ l) :
      Subobject.mk
        (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
          F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m d) h)).op)) =
      Subobject.mk
        (Abelian.image.ι (kernel.ι (α.hom.app (op (m + d))) ≫
          F.obj.map (homOfLE (Nat.le_add_right m d)).op)) := by
    exact (hc l m (by omega)).trans (hc (m + d) m (by omega)).symm
  have hSd (m : ℕ) : ∃ a : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + d))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m d)).op),
      a.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + d))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m d)).op) = j.app (op m) := by
    obtain ⟨a, ha⟩ := hS m
    let b := Subobject.isoOfMkEqMk
      (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op))
      (Abelian.image.ι (kernel.ι (α.hom.app (op (m + d))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m d)).op))
      (hc (m + d) m (by omega)).symm
    refine ⟨a ≪≫ b, ?_⟩
    simpa only [Iso.trans_hom, Category.assoc, b, Subobject.isoOfMkEqMk_hom,
      Subobject.ofMkLEMk_comp] using ha
  exact ⟨d, hd, S, j, hSd, K, ι, e, heq, hι, hker⟩

end AlgebraicGeometry
