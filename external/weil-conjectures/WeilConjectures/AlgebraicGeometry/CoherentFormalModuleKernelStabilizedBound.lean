/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelAffineBound
import WeilConjectures.AlgebraicGeometry.ModuleSubobjectEqOnCover

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A uniform bound for stabilization of the kernel images.

Source: Stacks Project, Lemma 087X, claims (a)--(b), affine Artin--Rees argument.
(blueprint: new-kernel-stabilized-bound).
The proof chooses a finite affine cover, applies Artin--Rees to the kernel on each
affine, and takes the maximum of the resulting bounds; equality of the resulting
quasi-coherent submodules is checked on the cover.
-/
theorem coherentFormalModule_kernel_stabilized_bound {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H) :
    ∃ c : ℕ, ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ (U.1 : Set X)) (fun U ↦ U.1.isOpen) (by
      intro x _
      obtain ⟨U, hxU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨U, hxU⟩, hx⟩)
  choose c hc using coherentFormalModule_kernel_affine_bound I F H α
  refine ⟨s.sup c, ?_⟩
  intro l m h
  apply module_subobject_eq_on_cover (fun U : s ↦ U.1.1)
    (by
      intro x
      obtain ⟨U, hx⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
      obtain ⟨hUs, hxU⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨U, hUs⟩, hxU⟩)
  intro U W hW
  have hbound : c U.1 ≤ s.sup c := Finset.le_sup U.2
  have hlocal : m + c U.1 ≤ m + s.sup c := Nat.add_le_add_left hbound m
  exact (hc U.1 l m (hlocal.trans h) W hW).trans
    (hc U.1 (m + s.sup c) m hlocal W hW).symm

end AlgebraicGeometry
