/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineOpenSectionsAdic
import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerCompletedScalarLimit
import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerFiniteLimit
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Completed linear projections of formal modules

Source: Stacks Project, Lemma 087X, affine description of K'_(l,m), using Lemma 087W.
(blueprint: lem-weil-pbc-formal-completed-projections-linear).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Lemma 087W and Lemma 087X.
(blueprint: lem-weil-pbc-formal-completed-projections-linear).

Build the completed modules from the section towers. The completion action is
coordinatewise, the finite-limit theorem supplies the projection kernels, and the
map of limits induced by alpha is completion-linear by checking every projection. -/
theorem coherentFormalModule_completed_projections_linear
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F H : CoherentFormalModule X I) (α : F ⟶ H) (U : X.affineOpens) :
    let A := Γ(X, U.1)
    let R := AdicCompletion (I.ideal U) A
    let J := (I.ideal U).map (algebraMap A R)
    ∃ (M N : ModuleCat.{u} R) (f : M ⟶ N),
      Module.Finite R M ∧ Module.Finite R N ∧
      ∃ (p : ∀ n : ℕ, ((ModuleCat.restrictScalars (algebraMap A R)).obj M)
          →ₗ[A] Γ(F.obj.obj (op n), U.1))
        (q : ∀ n : ℕ, N →+ Γ(H.obj.obj (op n), U.1)),
        (∀ n : ℕ, Function.Surjective (p n)) ∧
        (∀ (n : ℕ) (x : M), p n x = 0 ↔
          x ∈ J ^ (n + 1) • (⊤ : Submodule R M)) ∧
        (∀ (n : ℕ) (y : N), q n y = 0 ↔
          y ∈ J ^ (n + 1) • (⊤ : Submodule R N)) ∧
        (∀ (n : ℕ) (x : M), q n (f x) = (α.hom.app (op n)).app U.1 (p n x)) ∧
        (∀ (l m : ℕ) (h : m ≤ l) (x : M),
          p m x = (F.obj.map (homOfLE h).op).app U.1 (p l x)) := by
  classical
  let A := Γ(X, U.1)
  let K := I.ideal U
  let R := AdicCompletion K A
  let S := ModuleCat.restrictScalars (algebraMap A R)
  let G := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let TF := F.obj ⋙ G
  let TH := H.obj ⋙ G
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  have hF := coherentFormalModule_affine_open_sections_adic X I F U
  have hH := coherentFormalModule_affine_open_sections_adic X I H U
  obtain ⟨M, eM, hsM⟩ := ModuleCat.adicTower_completedScalarLimit A K TF hF.2.1
  obtain ⟨N, eN, hsN⟩ := ModuleCat.adicTower_completedScalarLimit A K TH hH.2.1
  have hM := ModuleCat.adicTower_finiteLimit A K TF hF.1 hF.2.1 hF.2.2 M eM hsM
  have hN := ModuleCat.adicTower_finiteLimit A K TH hH.1 hH.2.1 hH.2.2 N eN hsN
  let p (n : ℕ) : S.obj M ⟶ TF.obj (op n) := eM.hom ≫ limit.π TF (op n)
  let q (n : ℕ) : S.obj N ⟶ TH.obj (op n) := eN.hom ≫ limit.π TH (op n)
  let t : TF ⟶ TH := Functor.whiskerRight α.hom G
  let g : S.obj M ⟶ S.obj N := eM.hom ≫ lim.map t ≫ eN.inv
  have hg (n : ℕ) : g ≫ q n = p n ≫ t.app (op n) := by
    simp [g, p, q, Category.assoc]
  have hg_apply (n : ℕ) (x : M) : q n (g x) = t.app (op n) (p n x) :=
    congrArg (fun k ↦ k x) (hg n)
  have hlinear (r : R) (x : M) : g (r • x) = r • g x := by
    apply (ModuleCat.mono_iff_injective eN.hom).mp inferInstance
    apply Concrete.limit_ext TH
    intro j
    obtain ⟨n⟩ := j
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ K (n + 1) r)
    have hsp := hsM n r a x ha.symm
    have hsq := hsN n r a (g x) ha.symm
    change q n (g (r • x)) = q n (r • g x)
    change p n (r • x) = a • p n x at hsp
    change q n (r • g x) = a • q n (g x) at hsq
    rw [hsq, hg_apply, hsp, map_smul, hg_apply]
  let f : M ⟶ N := ModuleCat.ofHom
    { toFun := g
      map_add' := map_add g.hom
      map_smul' := hlinear }
  have hkernel (L : ModuleCat.{u} R) (n : ℕ) (x : L) :
      x ∈ K ^ (n + 1) • (⊤ : Submodule A (S.obj L)) ↔
      x ∈ (K.map (algebraMap A R)) ^ (n + 1) • (⊤ : Submodule R L) := by
    let : Module A L := Module.compHom L (algebraMap A R)
    let : IsScalarTower A R L := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    have he : (((K.map (algebraMap A R)) ^ (n + 1) •
        (⊤ : Submodule R L)).restrictScalars A) =
        K ^ (n + 1) • (⊤ : Submodule A L) := by
      rw [← Ideal.map_pow]
      exact Submodule.restrictScalars_map_smul_eq (K ^ (n + 1)) ⊤
    exact (SetLike.ext_iff.mp he x).symm
  refine ⟨M, N, f, hM.1, hN.1,
    (fun n ↦ (p n).hom), (fun n ↦ (q n).hom.toAddMonoidHom),
    (fun n ↦ (hM.2 n).1), ?_, ?_, ?_, ?_⟩
  · intro n x
    change p n x = 0 ↔ _
    rw [← hkernel M n x]
    exact SetLike.ext_iff.mp (hM.2 n).2 x
  · intro n y
    change q n y = 0 ↔ _
    rw [← hkernel N n y]
    exact SetLike.ext_iff.mp (hN.2 n).2 y
  · intro n x
    exact hg_apply n x
  · intro l m h x
    have hw : p l ≫ TF.map (homOfLE h).op = p m := by
      dsimp only [p]
      rw [Category.assoc, limit.w]
    exact (congrArg (fun k ↦ k x) hw).symm

end AlgebraicGeometry
