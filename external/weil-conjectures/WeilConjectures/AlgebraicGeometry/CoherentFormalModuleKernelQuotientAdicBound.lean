/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleShiftedQuotient
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelQuotientComparisonBound
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule

/-! # Artin--Rees bounds for stabilized kernel quotients

Source: Stacks Project, Lemma 087X.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry

/-- Sufficiently large shifts give a coherent adic quotient system.

Source: Stacks Project, Lemma 087X, claims (b)--(c).
(blueprint: lem-weil-pbc-formal-kernel-quotient-adic-bound).

Proof: Kernels and cokernels of maps between coherent modules are coherent. Apply
this twice to see that the abelian image of each kernel-transition map is coherent.
Transport its quasi-coherence and finite type along hS to S_m. Each shifted quotient
is therefore coherent by the proved coherence of completion quotients. The ideal
product on that quotient is zero by the cokernel multiplication calculation.
The eventual comparison bound supplies exactly the remaining successive reduction
condition. Combine these three clauses of IsCoherentFormalModule.
-/
theorem coherentFormalModule_kernel_quotient_adic_bound {X : Scheme.{u}} [IsNoetherian X]
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
      IsCoherentFormalModule I (formalShiftedQuotient I S d) := by
  have hclosure := (Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule X).1
  have hcoh (m : ℕ) : RingedSpace.IsCoherent X.toRingedSpace (S.obj (op m)) := by
    let f := kernel.ι (α.hom.app (op (m + c))) ≫
      F.obj.map (homOfLE (Nat.le_add_right m c)).op
    have hk : RingedSpace.IsCoherent X.toRingedSpace
        (kernel (α.hom.app (op (m + c)))) :=
      ((hclosure _ _ (F.property.1 (m + c)) (H.property.1 (m + c))).1 _).1
    have hC : RingedSpace.IsCoherent X.toRingedSpace (cokernel f) :=
      ((hclosure _ _ hk (F.property.1 m)).1 f).2
    have hA : RingedSpace.IsCoherent X.toRingedSpace (Abelian.image f) :=
      ((hclosure _ _ (F.property.1 m) hC).1 (cokernel.π f)).1
    obtain ⟨a, _⟩ := hS m
    have hprops := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp hA
    have : (Abelian.image f).IsQuasicoherent := hprops.1
    have : (Abelian.image f).IsFiniteType := hprops.2
    have : (S.obj (op m)).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso a.symm inferInstance
    have : (S.obj (op m)).IsFiniteType := isFiniteType_of_epi a.inv
    exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
      ⟨inferInstance, inferInstance⟩
  obtain ⟨b, hb⟩ := coherentFormalModule_kernel_quotient_comparison_bound I F H α c S j hc hS
  refine ⟨b, fun d hd ↦ ⟨?_, ?_, hb d hd⟩⟩
  · intro n
    exact (formalCompletionSystem_coherent I ⟨S.obj (op (n + d)), hcoh (n + d)⟩).1 n
  · intro n
    exact idealModuleProduct_quotient_zero (Scheme.idealSheafPower I.toModulesι (n + 1)).2

end AlgebraicGeometry
