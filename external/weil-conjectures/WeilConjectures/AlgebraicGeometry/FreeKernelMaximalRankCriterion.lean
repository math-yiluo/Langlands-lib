/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Maximal-rank kernels of finite free sheaf maps

Source: Stacks Project, Tags 0BDL and 0EWY, the local matrix argument and the rank
inequality for an injective free map.
(blueprint: lem-sc-free-kernel-maximal-rank-criterion).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

open Modules SheafOfModules

private noncomputable def sectionEquiv (X : Scheme.{u}) (M : X.Modules) :
    M.sections ≃ Γ(M, ⊤) where
  toFun s := s.val (.op ⊤)
  invFun x := M.val.sectionsMk
    (fun V ↦ M.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op x)
    (fun V W k ↦ by rw [← M.val.map_comp_apply]; congr 1)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    exact PresheafOfModules.sections_property s _
  right_inv x := by
    change M.val.map (𝟙 _) x = x
    simp

private noncomputable def freeHomTopEquiv (X : Scheme.{u}) (I : Type u) (M : X.Modules) :
    (free (R := X.ringCatSheaf) I ⟶ M) ≃ (I → Γ(M, ⊤)) :=
  M.freeHomEquiv.trans (Equiv.piCongrRight fun _ ↦ sectionEquiv X M)

private lemma matrix_injective {X : Scheme.{u}} {I J : Type u}
    [Finite J] [DecidableEq J] :
    Function.Injective (freeMatrix (X := X) (I := I) (J := J)) := by
  let := Fintype.ofFinite J
  intro p q hpq
  apply (freeHomTopEquiv X I (free J)).injective
  funext i
  apply (freeSectionsEquiv J).injective
  funext j
  exact congrArg (fun A ↦ A j i) hpq

private lemma matrix_comp {X : Scheme.{u}} {I J K : Type u}
    [Fintype J] [DecidableEq J] [Finite K] [DecidableEq K]
    (p : free (R := X.ringCatSheaf) I ⟶ free J) (q : free J ⟶ free K) :
    freeMatrix (p ≫ q) = freeMatrix q * freeMatrix p := by
  let := Fintype.ofFinite K
  ext k i
  change freeSectionsEquiv K
    (Modules.Hom.app q ⊤ (freeHomTopEquiv X I (free J) p i)) k = _
  rw [freeSectionsEquiv_app]
  rfl

private lemma matrix_mulVec_injective {X : Scheme.{u}} {I J : Type u}
    [Fintype I] [Finite J] [DecidableEq J]
    (p : free (R := X.ringCatSheaf) I ⟶ free J) [Mono p] :
    Function.Injective (Matrix.mulVec (freeMatrix p)) := by
  classical
  let := Fintype.ofFinite J
  have hp : Function.Injective (Modules.Hom.app p ⊤) := by
    change Function.Injective
      ((SheafOfModules.evaluation X.ringCatSheaf (.op ⊤)).map p)
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  intro a b hab
  apply (freeSectionsEquiv I).symm.injective
  apply hp
  apply (freeSectionsEquiv J).injective
  simpa only [freeSectionsEquiv_app, LinearEquiv.apply_symm_apply] using hab

private lemma square_mono_annihilator {X : Scheme.{u}} {I J : Type u}
    [Finite I] [Finite J]
    (p : free (R := X.ringCatSheaf) I ⟶ free I) [Mono p]
    (q : free (R := X.ringCatSheaf) I ⟶ free J) (hpq : p ≫ q = 0) : q = 0 := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  have hinj : Function.Injective (fun v ↦ Matrix.vecMul v (freeMatrix p)) :=
    Matrix.vecMul_injective_iff.mpr (Matrix.linearIndependent_col_iff_row.mp
      (Matrix.mulVec_injective_iff.mp (matrix_mulVec_injective p)))
  have hmat : freeMatrix q * freeMatrix p = 0 := by
    rw [← matrix_comp, hpq, freeMatrix_zero]
  apply matrix_injective
  rw [freeMatrix_zero]
  ext j i
  have hrow : freeMatrix q j = 0 := hinj (by
    funext k
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, mul_comm] using
      congrArg (fun A ↦ A j k) hmat)
  exact congrFun hrow i

private lemma free_mono_rank_le {X : Scheme.{u}} {r s : ℕ}
    [Nontrivial Γ(X, ⊤)]
    (p : free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      free (ULift.{u} (Fin s))) [Mono p] : r ≤ s := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (freeMatrix p).mulVecLin) (matrix_mulVec_injective p)
  simpa using h

set_option backward.isDefEq.respectTransparency false in
/-- For a finite free domain of rank at most r, a rank-r locally free kernel
forces the map to vanish and the domain rank to equal r unless the scheme is empty.
This is a sheaf-theoretic criterion on a fixed scheme, with no representability
or finite-presentation assertion.

Source: Stacks Project, Tag 0BDL, local matrix calculation using Tag 0EWY;
the strict-rank case uses the rank inequality for an injective free-module map.
(blueprint: lem-sc-free-kernel-maximal-rank-criterion).

Proof: Trivialize the rank-r kernel on an open cover, restrict the supplied
domain and target frames there, and take sections of its monomorphic inclusion.
When s=r this is an injective square matrix. Tag 0EWY makes its transpose
injective. Each coordinate of the outgoing map annihilates this inclusion,
so is in the kernel of the transpose and is zero. Thus the map is zero on
the cover and hence globally. If s<r, any point lies in a kernel-trivializing
chart with nontrivial ring of global sections. The injective map on sections
forces r <= s by the finite free-module rank inequality, a contradiction.
Thus the scheme is empty.
Conversely, a zero map has kernel isomorphic to its free domain, giving rank
r when s=r. On an empty scheme every sheaf is zero and locally free of every
rank, using the empty covering; every morphism is zero. Rank zero and the
zero-ring charts require no exception to these arguments. -/
theorem finiteLocallyFree_kernel_maximalRank_iff
    (X : Scheme.{u})
    (M N : SheafOfModules.{u} X.ringCatSheaf) (d : M ⟶ N)
    (s n r : ℕ) (hsr : s ≤ r)
    (hM : Nonempty (M ≅ SheafOfModules.free
      (R := X.ringCatSheaf) (ULift.{u} (Fin s))))
    (hN : Nonempty (N ≅ SheafOfModules.free
      (R := X.ringCatSheaf) (ULift.{u} (Fin n)))) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernel d) r ↔
      d = 0 ∧ (s = r ∨ IsEmpty X) := by
  classical
  constructor
  · intro hk
    have := hk
    obtain ⟨I, U, hU, eK⟩ :=
      Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free (kernel d) (r := r)
    let eDom (i : I) :=
      (Modules.restrictFunctor (U i).ι).mapIso hM.some ≪≫ restrictFreeIso (U i).ι _
    let eCod (i : I) :=
      (Modules.restrictFunctor (U i).ι).mapIso hN.some ≪≫ restrictFreeIso (U i).ι _
    let p (i : I) : free (R := (U i).toScheme.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
        free (ULift.{u} (Fin s)) :=
      (eK i).some.inv ≫ (Modules.restrictFunctor (U i).ι).map (kernel.ι d) ≫ (eDom i).hom
    have hp (i : I) : Mono (p i) := by
      have : Mono ((Modules.restrictFunctor (U i).ι).map (kernel.ι d)) := by
        let F := Modules.restrictFunctor (U i).ι
        have hmap : F.map (kernel.ι d) =
            (PreservesKernel.iso F d).hom ≫ kernel.ι (F.map d) := by
          rw [← PreservesKernel.iso_inv_ι]
          simp
        rw [hmap]
        infer_instance
      dsimp only [p]
      infer_instance
    by_cases heq : s = r
    · subst s
      refine ⟨hom_eq_zero_of_restrict d U hU (fun i ↦ ?_), Or.inl rfl⟩
      let q := (eDom i).inv ≫ (Modules.restrictFunctor (U i).ι).map d ≫ (eCod i).hom
      have hpq : p i ≫ q = 0 := by
        simp only [p, q, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
          kernel.condition]
        change (eK i).some.inv ≫ 0 ≫ (eCod i).hom = 0
        simp only [zero_comp, comp_zero]
      have hq := square_mono_annihilator (p i) q hpq
      simpa only [q, ← cancel_epi (eDom i).inv, ← cancel_mono (eCod i).hom,
        Category.assoc, comp_zero, zero_comp] using hq
    · have hempty : IsEmpty X := by
        refine ⟨fun x ↦ ?_⟩
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
          (hU.ge (Set.mem_univ x))
        have hnt : Nontrivial Γ((U i).toScheme, ⊤) := by
          by_contra h
          have hsub : Subsingleton Γ((U i).toScheme, ⊤) :=
            not_nontrivial_iff_subsingleton.mp h
          exact (Scheme.isEmpty_of_subsingleton_Γ hsub).false (⟨x, hi⟩ : U i)
        have hle := free_mono_rank_le (p i)
        exact heq (Nat.le_antisymm hsr hle)
      exact ⟨(isZero_of_isEmpty N).eq_of_tgt _ _, Or.inr hempty⟩
  · rintro ⟨hd, heq | hempty⟩
    · subst s
      subst d
      exact IsFiniteLocallyFreeOfRank.of_iso
        (hM.some.symm ≪≫ kernelZeroIsoSource.symm)
    · have := hempty
      apply isFiniteLocallyFreeOfRank_of_restrict_iso_free (kernel d)
        (ι := PEmpty.{u + 1}) (Y := fun _ ↦ X) (fun _ ↦ 𝟙 X)
      · apply eq_top_iff.mpr
        intro x _
        exact isEmptyElim x
      · intro i
        exact i.elim

end AlgebraicGeometry.Scheme
