/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
import WeilConjectures.AlgebraicGeometry.FormalKernelProductSection
import all WeilConjectures.AlgebraicGeometry.FormalKernelBilinearActionAssociative

/-! # Bilinear multiplication on formal kernel pieces

Source: Stacks Project, Lemma 087Z and Section 0EHN.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable local instance restrictedSectionModule {X : Scheme.{u}}
    (M : X.Modules) {U V : X.Opens} (i : U ⟶ V) :
    Module Γ(X, U)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i.op).hom).obj
        (M.val.obj (op U))) :=
  inferInstanceAs (Module Γ(X, U) (M.val.obj (op U)))

set_option backward.isDefEq.respectTransparency false in
private theorem component_add {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (a b : M.val.obj (op U)) :
    f.val.app (op U) (a + b) = f.val.app (op U) a + f.val.app (op U) b := by
  exact (f.val.app (op U)).hom.map_add a b

set_option backward.isDefEq.respectTransparency false in
private theorem component_smul {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (r : Γ(X, U)) (a : M.val.obj (op U)) :
    f.val.app (op U) (r • a) = r • f.val.app (op U) a := by
  exact (f.val.app (op U)).hom.map_smul r a

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_add {X : Scheme.{u}} (M : X.Modules)
    (U V : X.Opens) (h : V ≤ U) (a b : M.val.obj (op U)) :
    M.val.map (homOfLE h).op (a + b) =
      M.val.map (homOfLE h).op a + M.val.map (homOfLE h).op b := by
  exact (M.val.map (homOfLE h).op).hom.map_add a b

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_smul {X : Scheme.{u}} (M : X.Modules)
    (U V : X.Opens) (h : V ≤ U) (r : Γ(X, U)) (s : M.val.obj (op U)) :
    M.val.map (homOfLE h).op (r • s) =
      (X.presheaf.map (homOfLE h).op).hom r • M.val.map (homOfLE h).op s := by
  exact M.val.map_smul (homOfLE h).op r s

set_option backward.isDefEq.respectTransparency false in
private theorem sections_eq_of_local {X : Scheme.{u}} (K : X.Modules) (U : X.Opens)
    (s t : K.val.obj (op U))
    (hlocal : ∀ (p : X), p ∈ U → ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
      K.val.map (homOfLE hVU).op s = K.val.map (homOfLE hVU).op t) : s = t := by
  classical
  choose V hVU hpV heq using fun p : U ↦ hlocal p.val p.property
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨K.presheaf, K.isSheaf⟩ V U
    (fun p ↦ homOfLE (hVU p))
  · intro p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩
  · intro p
    exact heq p

set_option backward.isDefEq.respectTransparency false in
/-- Bilinear action maps on formal kernels, before imposing any algebra laws.
Source: Stacks Project, Lemma 087Z, its associated graded module construction,
and Section 0EHN; https://stacks.math.columbia.edu/tag/087Z.
(blueprint: lem-weil-pbc-formal-kernel-bilinear-action-exists).

Proof: The product-section lemma supplies, for each fixed a and x, the unique
kernel section satisfying all local representative equations. Choose this unique
section as out(a,x). Restriction preserves its equations by functoriality, so
uniqueness proves restriction compatibility. The equation on U itself, with the
identity restriction, proves the formula for a given global representative and lift.
The adjacent formal transitions are quotient projections followed by isomorphisms,
hence epis; induction proves that every transition is epi. Quotient projections
for the coefficients are also epis. The local surjectivity theorem for sheaves
therefore gives simultaneous lifts of any three input sections near each point.
For addition in the first variable lift both coefficients and one kernel section;
the sum of the coefficients lifts their sum. Apply the product formula three times
and use distributivity. For addition in the second variable lift one coefficient
and both kernel sections; the sum of the lifts lifts the sum, and distributivity
again compares the outputs. For scalar multiplication restrict the scalar to the
smaller open and multiply the coefficient lift, or the kernel lift, by it. The
product formula and the associativity and commutativity of scalar multiplication
compare the outputs. Each comparison is an equality after the kernel inclusion,
which is injective on sections. Sheaf separation turns these local equalities into
the four global linearity identities. LinearMap.mk₂ packages them into the requested
bilinear maps; the already proved restriction and product equations finish.
Empty opens use the empty-cover separation argument, and degree zero uses the
identity kernel inclusion. No arbitrary global lifting of an epimorphism is used. -/
theorem formalKernel_bilinear_action_exists {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) :
    ∃ act : ∀ (m n : ℕ) (U : X.Opens),
      (formalAssociatedGradedPiece I m).val.obj (op U) →ₗ[Γ(X, U)]
        (formalKernelPiece F n).val.obj (op U) →ₗ[Γ(X, U)]
          (formalKernelPiece F (m + n)).val.obj (op U),
      (∀ (m n : ℕ) (U V : X.Opens) (h : V ≤ U)
        (a : (formalAssociatedGradedPiece I m).val.obj (op U))
        (x : (formalKernelPiece F n).val.obj (op U)),
      (formalKernelPiece F (m + n)).val.map (homOfLE h).op (act m n U a x) =
        act m n V ((formalAssociatedGradedPiece I m).val.map (homOfLE h).op a)
          ((formalKernelPiece F n).val.map (homOfLE h).op x)) ∧
      (∀ (m n : ℕ) (U : X.Opens)
          (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
          (x : (formalKernelPiece F n).val.obj (op U))
          (t : (F.obj.obj (op (m + n))).val.obj (op U)),
          (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
            (formalKernelι F n).val.app (op U) x →
          (formalKernelι F (m + n)).val.app (op U)
            (act m n U ((formalAssociatedGradedπ I m).val.app (op U) a) x) =
              (@id Γ(X, U)
                ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t) := by
  classical
  let out (m n : ℕ) (U : X.Opens)
      (a : (formalAssociatedGradedPiece I m).val.obj (op U))
      (x : (formalKernelPiece F n).val.obj (op U)) :=
    (formalKernel_product_section_existsUnique I F m n U a x).exists.choose
  have hout (m n : ℕ) (U : X.Opens)
      (a : (formalAssociatedGradedPiece I m).val.obj (op U))
      (x : (formalKernelPiece F n).val.obj (op U)) :=
    (formalKernel_product_section_existsUnique I F m n U a x).exists.choose_spec
  have hnat (m n : ℕ) (U V : X.Opens) (h : V ≤ U)
      (a : (formalAssociatedGradedPiece I m).val.obj (op U))
      (x : (formalKernelPiece F n).val.obj (op U)) :
      (formalKernelPiece F (m + n)).val.map (homOfLE h).op (out m n U a x) =
        out m n V ((formalAssociatedGradedPiece I m).val.map (homOfLE h).op a)
          ((formalKernelPiece F n).val.map (homOfLE h).op x) := by
    apply (formalKernel_product_section_existsUnique I F m n V
      ((formalAssociatedGradedPiece I m).val.map (homOfLE h).op a)
      ((formalKernelPiece F n).val.map (homOfLE h).op x)).unique
    · intro W hWV a' t ha ht
      rw [← (formalKernelPiece F (m + n)).val.map_comp_apply]
      apply hout m n U a x W (hWV.trans h) a' t
      · rw [← PresheafOfModules.map_comp_apply] at ha
        exact ha
      · rw [← PresheafOfModules.map_comp_apply] at ht
        exact ht
    · exact hout m n V _ _
  have hformula (m n : ℕ) (U : X.Opens)
      (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
      (x : (formalKernelPiece F n).val.obj (op U))
      (t : (F.obj.obj (op (m + n))).val.obj (op U))
      (ht : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
        (formalKernelι F n).val.app (op U) x) :
      (formalKernelι F (m + n)).val.app (op U)
        (out m n U ((formalAssociatedGradedπ I m).val.app (op U) a) x) =
          (@id Γ(X, U)
            ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t := by
    have h := hout m n U ((formalAssociatedGradedπ I m).val.app (op U) a) x
      U le_rfl a t
    simpa using h (by simp) (by simpa using ht)
  have hq (m : ℕ) : Epi (formalAssociatedGradedπ I m) := by
    unfold formalAssociatedGradedπ formalModuleQuotientπ
    infer_instance
  have ht (m n : ℕ) : Epi (F.obj.map (homOfLE (Nat.le_add_left n m)).op) :=
    formal_transition_epi F _
  have hadd_left (m n : ℕ) (U : X.Opens) (a b : (formalAssociatedGradedPiece I m).val.obj (op U))
      (x : (formalKernelPiece F n).val.obj (op U)) :
      out m n U (a + b) x = out m n U a x + out m n U b x := by
    apply sections_eq_of_local (formalKernelPiece F (m + n)) U
    intro p hp
    obtain ⟨V, hVU, hpV, a', b', t, ha, hb, ht⟩ := local_lifts_three
      (formalAssociatedGradedπ I m) (formalAssociatedGradedπ I m)
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op)
      U a b ((formalKernelι F n).val.app (op U) x) p hp
    refine ⟨V, hVU, hpV, ?_⟩
    have hx : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) t =
        (formalKernelι F n).val.app (op V)
          ((formalKernelPiece F n).val.map (homOfLE hVU).op x) := by
      rw [PresheafOfModules.naturality_apply]
      exact ht
    simp only [restriction_add, hnat]
    apply kernel_inclusion_injective F (m + n) V
    rw [component_add (formalKernelι F (m + n)) V]
    rw [← ha, ← hb,
      ← component_add (formalAssociatedGradedπ I m) V]
    rw [hformula m n V (a' + b') _ t hx,
      hformula m n V a' _ t hx, hformula m n V b' _ t hx]
    rw [component_add (Scheme.idealSheafPower I.toModulesι m).2 V]
    exact add_smul _ _ _
  have hsmul_left (m n : ℕ) (U : X.Opens) (r : Γ(X, U))
      (a : (formalAssociatedGradedPiece I m).val.obj (op U))
      (x : (formalKernelPiece F n).val.obj (op U)) :
      out m n U (r • a) x = r • out m n U a x := by
    apply sections_eq_of_local (formalKernelPiece F (m + n)) U
    intro p hp
    obtain ⟨V, hVU, hpV, a', b', t, ha, hb, ht⟩ := local_lifts_three
      (formalAssociatedGradedπ I m) (formalAssociatedGradedπ I m)
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op)
      U a a ((formalKernelι F n).val.app (op U) x) p hp
    refine ⟨V, hVU, hpV, ?_⟩
    have hx : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) t =
        (formalKernelι F n).val.app (op V)
          ((formalKernelPiece F n).val.map (homOfLE hVU).op x) := by
      rw [PresheafOfModules.naturality_apply]
      exact ht
    simp only [restriction_smul, hnat]
    apply kernel_inclusion_injective F (m + n) V
    rw [component_smul (formalKernelι F (m + n)) V]
    rw [← ha, ← component_smul (formalAssociatedGradedπ I m) V]
    rw [hformula m n V (_ • a') _ t hx, hformula m n V a' _ t hx]
    rw [component_smul (Scheme.idealSheafPower I.toModulesι m).2 V]
    exact mul_smul _ _ _
  have hadd_right (m n : ℕ) (U : X.Opens) (a : (formalAssociatedGradedPiece I m).val.obj (op U))
      (x y : (formalKernelPiece F n).val.obj (op U)) :
      out m n U a (x + y) = out m n U a x + out m n U a y := by
    apply sections_eq_of_local (formalKernelPiece F (m + n)) U
    intro p hp
    obtain ⟨V, hVU, hpV, a', b', t, ha, hb, ht⟩ := local_lifts_three
      (formalAssociatedGradedπ I m)
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op)
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op)
      U a ((formalKernelι F n).val.app (op U) x)
        ((formalKernelι F n).val.app (op U) y) p hp
    refine ⟨V, hVU, hpV, ?_⟩
    have hx : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) b' =
        (formalKernelι F n).val.app (op V)
          ((formalKernelPiece F n).val.map (homOfLE hVU).op x) := by
      rw [PresheafOfModules.naturality_apply]
      exact hb
    have hy : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) t =
        (formalKernelι F n).val.app (op V)
          ((formalKernelPiece F n).val.map (homOfLE hVU).op y) := by
      rw [PresheafOfModules.naturality_apply]
      exact ht
    have hxy : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) (b' + t) =
        (formalKernelι F n).val.app (op V)
          ((formalKernelPiece F n).val.map (homOfLE hVU).op x +
            (formalKernelPiece F n).val.map (homOfLE hVU).op y) := by
      rw [component_add (F.obj.map (homOfLE (Nat.le_add_left n m)).op) V,
        component_add (formalKernelι F n) V, hx, hy]
    simp only [restriction_add, hnat]
    apply kernel_inclusion_injective F (m + n) V
    rw [component_add (formalKernelι F (m + n)) V]
    rw [← ha, hformula m n V a' _ (b' + t) hxy,
      hformula m n V a' _ b' hx, hformula m n V a' _ t hy]
    exact smul_add _ _ _
  have hsmul_right (m n : ℕ) (U : X.Opens) (r : Γ(X, U))
      (a : (formalAssociatedGradedPiece I m).val.obj (op U))
      (x : (formalKernelPiece F n).val.obj (op U)) :
      out m n U a (r • x) = r • out m n U a x := by
    apply sections_eq_of_local (formalKernelPiece F (m + n)) U
    intro p hp
    obtain ⟨V, hVU, hpV, a', b', t, ha, hb, ht⟩ := local_lifts_three
      (formalAssociatedGradedπ I m)
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op)
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op)
      U a ((formalKernelι F n).val.app (op U) x)
        ((formalKernelι F n).val.app (op U) x) p hp
    refine ⟨V, hVU, hpV, ?_⟩
    have hx : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) b' =
        (formalKernelι F n).val.app (op V)
          ((formalKernelPiece F n).val.map (homOfLE hVU).op x) := by
      rw [PresheafOfModules.naturality_apply]
      exact hb
    have hrx : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V)
        ((X.presheaf.map (homOfLE hVU).op).hom r • b') =
        (formalKernelι F n).val.app (op V)
          ((X.presheaf.map (homOfLE hVU).op).hom r •
            (formalKernelPiece F n).val.map (homOfLE hVU).op x) := by
      rw [component_smul (F.obj.map (homOfLE (Nat.le_add_left n m)).op) V,
        component_smul (formalKernelι F n) V, hx]
    simp only [restriction_smul, hnat]
    apply kernel_inclusion_injective F (m + n) V
    rw [component_smul (formalKernelι F (m + n)) V]
    rw [← ha, hformula m n V a' _ (_ • b') hrx, hformula m n V a' _ b' hx]
    exact smul_comm _ _ _
  let act (m n : ℕ) (U : X.Opens) :=
    LinearMap.mk₂ Γ(X, U) (out m n U) (hadd_left m n U)
      (hsmul_left m n U) (hadd_right m n U) (hsmul_right m n U)
  refine ⟨act, ?_, ?_⟩
  · exact hnat
  · exact hformula

end AlgebraicGeometry
