/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
import all WeilConjectures.AlgebraicGeometry.FormalKernelBilinearActionAssociative
import WeilConjectures.AlgebraicGeometry.FormalKernelRepresentativeProduct
import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk

/-! # A product section determined by local representatives

Source: Stacks Project, Lemma 087Z and Section 0EHN.
(blueprint: lem-weil-pbc-formal-kernel-product-section).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private def ProductEquation {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (m n : ℕ) (U : X.Opens)
    (a : (formalAssociatedGradedPiece I m).val.obj (op U))
    (x : (formalKernelPiece F n).val.obj (op U))
    (y : (formalKernelPiece F (m + n)).val.obj (op U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U)
        (a' : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op V))
        (t : (F.obj.obj (op (m + n))).val.obj (op V)),
        (formalAssociatedGradedπ I m).val.app (op V) a' =
          (formalAssociatedGradedPiece I m).val.map (homOfLE h).op a →
        (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) t =
          (formalKernelι F n).val.app (op V)
            ((formalKernelPiece F n).val.map (homOfLE h).op x) →
        (formalKernelι F (m + n)).val.app (op V)
          ((formalKernelPiece F (m + n)).val.map (homOfLE h).op y) =
            (@id Γ(X, V)
              ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op V) a')) • t

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_comp {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (s : M.val.obj (op U)) :
    M.val.map (homOfLE hWV).op (M.val.map (homOfLE hVU).op s) =
      M.val.map (homOfLE (hWV.trans hVU)).op s := by
  rw [← PresheafOfModules.map_comp_apply]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private theorem equation_restrict {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (m n : ℕ)
    (U V : X.Opens) (h : V ≤ U)
    (a : (formalAssociatedGradedPiece I m).val.obj (op U))
    (x : (formalKernelPiece F n).val.obj (op U))
    (y : (formalKernelPiece F (m + n)).val.obj (op U))
    (hy : ProductEquation I F m n U a x y) :
    ProductEquation I F m n V
      ((formalAssociatedGradedPiece I m).val.map (homOfLE h).op a)
      ((formalKernelPiece F n).val.map (homOfLE h).op x)
      ((formalKernelPiece F (m + n)).val.map (homOfLE h).op y) := by
  intro W hWV b t hb ht
  rw [← PresheafOfModules.map_comp_apply]
  apply hy W (hWV.trans h) b t
  · rw [← PresheafOfModules.map_comp_apply] at hb
    exact hb
  · rw [← PresheafOfModules.map_comp_apply] at ht
    exact ht

set_option backward.isDefEq.respectTransparency false in
private theorem equation_unique {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (m n : ℕ) (U : X.Opens)
    (a : (formalAssociatedGradedPiece I m).val.obj (op U))
    (x : (formalKernelPiece F n).val.obj (op U))
    (y z : (formalKernelPiece F (m + n)).val.obj (op U))
    (hy : ProductEquation I F m n U a x y)
    (hz : ProductEquation I F m n U a x z) : y = z := by
  classical
  have : Epi (formalAssociatedGradedπ I m) := by
    unfold formalAssociatedGradedπ formalModuleQuotientπ
    infer_instance
  have : Epi (F.obj.map (homOfLE (Nat.le_add_left n m)).op) :=
    formal_transition_epi F _
  have hlocal (p : U) : ∃ (V : X.Opens) (hVU : V ≤ U), p.val ∈ V ∧
      (formalKernelPiece F (m + n)).val.map (homOfLE hVU).op y =
        (formalKernelPiece F (m + n)).val.map (homOfLE hVU).op z := by
    obtain ⟨V, hVU, hpV, a', _, t, ha, _, ht⟩ := local_lifts_three
      (formalAssociatedGradedπ I m) (formalAssociatedGradedπ I m)
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op)
      U a a ((formalKernelι F n).val.app (op U) x) p.val p.property
    rw [← PresheafOfModules.naturality_apply] at ht
    refine ⟨V, hVU, hpV, kernel_inclusion_injective F (m + n) V ?_⟩
    exact (hy V hVU a' t ha ht).trans (hz V hVU a' t ha ht).symm
  choose V hVU hpV heq using hlocal
  apply TopCat.Sheaf.eq_of_locally_eq'
    ⟨(formalKernelPiece F (m + n)).presheaf, (formalKernelPiece F (m + n)).isSheaf⟩
    V U (fun p ↦ homOfLE (hVU p))
  · intro p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩
  · exact heq

set_option backward.isDefEq.respectTransparency false in
private theorem coefficient_restrict {X : Scheme.{u}} (I : X.IdealSheafData)
    (m : ℕ) (U V : X.Opens) (h : V ≤ U)
    (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U)) :
    (X.ringCatSheaf.obj.map (homOfLE h).op)
        (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) =
      (@id Γ(X, V) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op V)
        ((Scheme.idealSheafPower I.toModulesι m).1.val.map (homOfLE h).op a))) := by
  exact (PresheafOfModules.naturality_apply
    (Scheme.idealSheafPower I.toModulesι m).2.val (homOfLE h).op a).symm

set_option backward.isDefEq.respectTransparency false in
private theorem equation_of_representatives {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (m n : ℕ) (U : X.Opens)
    (a : (formalAssociatedGradedPiece I m).val.obj (op U))
    (x : (formalKernelPiece F n).val.obj (op U))
    (a' : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
    (t : (F.obj.obj (op (m + n))).val.obj (op U))
    (ha : (formalAssociatedGradedπ I m).val.app (op U) a' = a)
    (ht : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
      (formalKernelι F n).val.app (op U) x) :
    ∃ y, ProductEquation I F m n U a x y := by
  obtain ⟨⟨y, hy⟩, _⟩ := formalKernel_representative_product I F m n U a' x t ht
  refine ⟨y, ?_⟩
  intro V hVU b s hb hs
  let av := (Scheme.idealSheafPower I.toModulesι m).1.val.map (homOfLE hVU).op a'
  let tv := (F.obj.obj (op (m + n))).val.map (homOfLE hVU).op t
  have htv : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) tv =
      (formalKernelι F n).val.app (op V)
        ((formalKernelPiece F n).val.map (homOfLE hVU).op x) := by
    dsimp [tv]
    rw [PresheafOfModules.naturality_apply, ht, PresheafOfModules.naturality_apply]
  have hav : (formalAssociatedGradedπ I m).val.app (op V) av =
      (formalAssociatedGradedPiece I m).val.map (homOfLE hVU).op a := by
    dsimp [av]
    rw [PresheafOfModules.naturality_apply, ha]
  have hind := (formalKernel_representative_product I F m n V av
    ((formalKernelPiece F n).val.map (homOfLE hVU).op x) tv htv).2 b s
      (hb.trans hav.symm) hs
  rw [PresheafOfModules.naturality_apply, hy,
    (F.obj.obj (op (m + n))).val.map_smul]
  rw [coefficient_restrict]
  exact hind.symm

set_option backward.isDefEq.respectTransparency false in
/-- For two fixed sections, the local multiplication equations determine one output.
No linear map or compatibility between different pairs of inputs is asserted.
Source: Stacks Project, Lemma 087Z and Section 0EHN, the associated graded construction;
https://stacks.math.columbia.edu/tag/087Z.
(blueprint: lem-weil-pbc-formal-kernel-product-section).

Proof: On stalks, induct through the adjacent quotient isomorphisms of F. Reducing
level r+1 to level n+1 is quotient by I^(n+1): iterated quotients by nested ideal
powers agree with the quotient by the smaller power. Every transition is therefore
a sheaf epimorphism. Locally lift a to a' in I^m and the inclusion of x to t at
level m+n+1. If n>0, t reduces to zero at level n and thus belongs to I^n times
that level. If n=0, use I^0 F=F. Consequently a't belongs to I^(m+n) F and has a
unique preimage in the kernel K_(m+n); for m+n=0 use the identity inclusion.
Changing t by I^(n+1) F changes a't by I^(m+n+1) F=0. Changing a' by I^(m+1)
has the same effect, since t belongs to I^n F. Thus the local kernel preimages
agree on overlaps and glue by the sheaf axiom. On any smaller open, compare its
specified representatives with the restrictions of the original local ones;
independence and sheaf separation give the displayed equation. For uniqueness,
locally lift a and x around every point. Both proposed outputs have the same
image a't under the kernel inclusion, which is injective on sections. Sheaf
separation equates the outputs. On an empty open the cover is empty and separation
still applies. Zero degrees, the zero ideal, the unit ideal, and zero modules need
no exception to this argument. -/
theorem formalKernel_product_section_existsUnique {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (m n : ℕ) (U : X.Opens)
    (a : (formalAssociatedGradedPiece I m).val.obj (op U))
    (x : (formalKernelPiece F n).val.obj (op U)) :
    ∃! y : (formalKernelPiece F (m + n)).val.obj (op U),
      ∀ (V : X.Opens) (h : V ≤ U)
        (a' : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op V))
        (t : (F.obj.obj (op (m + n))).val.obj (op V)),
        (formalAssociatedGradedπ I m).val.app (op V) a' =
          (formalAssociatedGradedPiece I m).val.map (homOfLE h).op a →
        (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) t =
          (formalKernelι F n).val.app (op V)
            ((formalKernelPiece F n).val.map (homOfLE h).op x) →
        (formalKernelι F (m + n)).val.app (op V)
          ((formalKernelPiece F (m + n)).val.map (homOfLE h).op y) =
            (@id Γ(X, V)
              ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op V) a')) • t := by
  classical
  have : Epi (formalAssociatedGradedπ I m) := by
    unfold formalAssociatedGradedπ formalModuleQuotientπ
    infer_instance
  have : Epi (F.obj.map (homOfLE (Nat.le_add_left n m)).op) :=
    formal_transition_epi F _
  have hlocal (p : U) : ∃ (V : X.Opens) (hVU : V ≤ U), p.val ∈ V ∧
      ∃ y, ProductEquation I F m n V
        ((formalAssociatedGradedPiece I m).val.map (homOfLE hVU).op a)
        ((formalKernelPiece F n).val.map (homOfLE hVU).op x) y := by
    obtain ⟨V, hVU, hpV, a', _, t, ha, _, ht⟩ := local_lifts_three
      (formalAssociatedGradedπ I m) (formalAssociatedGradedπ I m)
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op)
      U a a ((formalKernelι F n).val.app (op U) x) p.val p.property
    rw [← PresheafOfModules.naturality_apply] at ht
    exact ⟨V, hVU, hpV, equation_of_representatives I F m n V _ _ a' t ha ht⟩
  choose V hVU hpV y hy using hlocal
  have hcover : U ≤ iSup V := by
    intro p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩
  have hcompat : (formalKernelPiece F (m + n)).presheaf.IsCompatible V y := by
    intro p q
    change (formalKernelPiece F (m + n)).val.map (homOfLE inf_le_left).op (y p) =
      (formalKernelPiece F (m + n)).val.map (homOfLE inf_le_right).op (y q)
    apply equation_unique I F m n (V p ⊓ V q)
      ((formalAssociatedGradedPiece I m).val.map
        (homOfLE (inf_le_left.trans (hVU p))).op a)
      ((formalKernelPiece F n).val.map
        (homOfLE (inf_le_left.trans (hVU p))).op x)
    · have h := equation_restrict I F m n (V p) (V p ⊓ V q)
        inf_le_left _ _ _ (hy p)
      simpa only [restriction_comp] using h
    · have h := equation_restrict I F m n (V q) (V p ⊓ V q)
        inf_le_right _ _ _ (hy q)
      simpa only [restriction_comp] using h
  obtain ⟨out, hout, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(formalKernelPiece F (m + n)).presheaf, (formalKernelPiece F (m + n)).isSheaf⟩
    V U (fun p ↦ homOfLE (hVU p)) hcover y hcompat
  change ∀ p, (formalKernelPiece F (m + n)).val.map (homOfLE (hVU p)).op out = y p
    at hout
  have houtEq : ProductEquation I F m n U a x out := by
    intro W hWU b t hb ht
    apply TopCat.Sheaf.eq_of_locally_eq'
      ⟨(F.obj.obj (op (m + n))).presheaf, (F.obj.obj (op (m + n))).isSheaf⟩
      (fun p ↦ W ⊓ V p) W (fun _ ↦ homOfLE inf_le_left)
    · intro p hp
      exact TopologicalSpace.Opens.mem_iSup.mpr
        ⟨⟨p, hWU hp⟩, hp, hpV ⟨p, hWU hp⟩⟩
    · intro p
      change (F.obj.obj (op (m + n))).val.map (homOfLE inf_le_left).op
          ((formalKernelι F (m + n)).val.app (op W)
            ((formalKernelPiece F (m + n)).val.map (homOfLE hWU).op out)) =
        (F.obj.obj (op (m + n))).val.map (homOfLE inf_le_left).op
          ((@id Γ(X, W)
            ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op W) b)) • t)
      rw [← PresheafOfModules.naturality_apply, restriction_comp]
      have houtW : (formalKernelPiece F (m + n)).val.map
          (homOfLE (inf_le_left.trans hWU) : W ⊓ V p ⟶ U).op out =
          (formalKernelPiece F (m + n)).val.map
            (homOfLE inf_le_right : W ⊓ V p ⟶ V p).op (y p) := by
        rw [← hout p, restriction_comp]
      rw [houtW]
      rw [(F.obj.obj (op (m + n))).val.map_smul, coefficient_restrict]
      apply hy p (W ⊓ V p) inf_le_right
        ((Scheme.idealSheafPower I.toModulesι m).1.val.map
          (homOfLE inf_le_left).op b)
        ((F.obj.obj (op (m + n))).val.map (homOfLE inf_le_left).op t)
      · rw [PresheafOfModules.naturality_apply, hb,
          ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
        rfl
      · rw [PresheafOfModules.naturality_apply, ht,
          ← PresheafOfModules.naturality_apply,
          ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
        rfl
  exact ⟨out, houtEq, fun z hz ↦ equation_unique I F m n U a x z out hz houtEq⟩

end AlgebraicGeometry
