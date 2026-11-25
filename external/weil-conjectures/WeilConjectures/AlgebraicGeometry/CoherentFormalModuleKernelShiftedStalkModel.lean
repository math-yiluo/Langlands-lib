/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleShiftedQuotient
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelStalkPresentation
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Local quotient models for shifted stabilized kernels

Source: Stacks Project, Lemma 087X, proof of claims (a) and (b).
(blueprint: lem-weil-pbc-formal-kernel-shifted-stalk-model).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

/-- After a uniform shift, the stalk system is the power-quotient system of a module.

Source: Stacks Project, Lemma 087X, proof of claims (a) and (b).
(blueprint: lem-weil-pbc-formal-kernel-shifted-stalk-model).

Proof: Apply the compatible stalk presentation theorem to obtain p_m : M -> S_m
 with the uniform bound on ker p_(n+d). The stalk q_n of the defining quotient
 projection is surjective with kernel J^(n+1) S_(n+d), by exactness of stalks
 and the stalk formula for ideal powers and their products. Since p_(n+d) is
 surjective, the composite f_n = q_n p_(n+d) is surjective and its kernel is
 J^(n+1) M + ker p_(n+d). The bound makes this sum just J^(n+1) M.
 The first isomorphism theorem therefore gives M/J^(n+1) M isomorphic to
 the stalk of the shifted quotient. Use its inverse for E_n. To check the
 transition equation, lift a stalk section along f_(n+1); the cokernel
 equation for formalModuleQuotientMap and compatibility of p reduce both
 sides to the class of the same element of M. This also applies to zero
 and unit ideals, zero modules, and the empty scheme. -/
theorem coherentFormalModule_kernel_shifted_stalk_model
    {X : Scheme.{u}} [IsNoetherian X]
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
    ∃ b : ℕ, ∀ d : ℕ, max c b ≤ d → ∀ x : X,
      ∀ e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          (SheafOfModules.unit X.ringCatSheaf) ≅
          ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      (∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r) →
      let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
      let J : Ideal (X.presheaf.stalk x) := LinearMap.range (T.map I.toModulesι ≫ e.hom).hom
      ∃ M : ModuleCat.{u} (X.presheaf.stalk x),
        ∃ E : ∀ n : ℕ, T.obj ((formalShiftedQuotient I S d).obj (op n)) ≃ₗ[
            X.presheaf.stalk x] (M ⧸ J ^ (n + 1) • (⊤ : Submodule _ M)),
          ∀ (n : ℕ) (z : T.obj ((formalShiftedQuotient I S d).obj (op (n + 1)))),
            E n ((T.map ((formalShiftedQuotient I S d).map
              (homOfLE (Nat.le_succ n)).op)).hom z) =
              Submodule.factorPow J M (Nat.le_succ (n + 1)) (E (n + 1) z)  := by
  obtain ⟨b, hb⟩ := coherentFormalModule_kernel_stalk_presentation I F H α c S j hc hS
  refine ⟨b, ?_⟩
  intro d hd x e he
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let J : Ideal (X.presheaf.stalk x) := LinearMap.range (T.map I.toModulesι ≫ e.hom).hom
  obtain ⟨M, p, hsurj, htrans, hbound⟩ := hb x e he
  let q (n : ℕ) := (T.map (formalModuleQuotientπ I (n + 1)
    (S.obj (op (n + d))))).hom
  have hq (n : ℕ) : Function.Surjective (q n) ∧
      LinearMap.ker (q n) = J ^ (n + 1) • (⊤ : Submodule _ (T.obj (S.obj (op (n + d))))) := by
    obtain ⟨e', he', _, _, _, _, hp⟩ := Scheme.ideal_module_product_stalk
      I.toModulesι (S.obj (op (n + d))) x
    have heq : e'.hom = e.hom := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      obtain ⟨U, hx, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf z
      rw [he' U hx r, he U hx r]
    obtain ⟨_, hr, _⟩ := hp (n + 1) (Nat.succ_pos n)
    rw [heq] at hr
    obtain ⟨hs, hex⟩ := (RingedSpace.module_stalk_exact X.toRingedSpace
      (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
        (S.obj (op (n + d))))).2.2.1 x
    refine ⟨(ModuleCat.epi_iff_surjective _).mp hs, ?_⟩
    exact hex.moduleCat_range_eq_ker.symm.trans hr
  let f (n : ℕ) := (q n).comp (p (n + d))
  have hf (n : ℕ) : Function.Surjective (f n) := (hq n).1.comp (hsurj (n + d))
  have hk (n : ℕ) : LinearMap.ker (f n) = J ^ (n + 1) • (⊤ : Submodule _ M) := by
    rw [LinearMap.ker_comp, (hq n).2,
      Submodule.comap_smul_top_of_surjective _ _ (hsurj (n + d)),
      sup_eq_left.mpr (hbound d hd n)]
  let a (n : ℕ) : (M ⧸ J ^ (n + 1) • (⊤ : Submodule _ M)) ≃ₗ[
      X.presheaf.stalk x] T.obj ((formalShiftedQuotient I S d).obj (op n)) :=
    (Submodule.quotEquivOfEq _ _ (hk n).symm).trans
      ((f n).quotKerEquivOfSurjective (hf n))
  have ha (n : ℕ) (z : M) : a n (Submodule.Quotient.mk z) = f n z := by
    exact (f n).quotKerEquivOfSurjective_apply_mk (hf n) z
  refine ⟨M, fun n ↦ (a n).symm, ?_⟩
  intro n z
  obtain ⟨m, rfl⟩ := hf (n + 1) z
  have ht : (T.map ((formalShiftedQuotient I S d).map
      (homOfLE (Nat.le_succ n)).op)).hom (f (n + 1) m) = f n m := by
    have hfac : formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + d))) ≫
        (formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op =
        S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) d)).op ≫
          formalModuleQuotientπ I (n + 1) (S.obj (op (n + d))) := by
      simp only [formalShiftedQuotient, formalModuleQuotientMap,
        formalModuleQuotientπ, cokernel.π_desc]
    have h := congrArg (fun k ↦ (T.map k).hom (p (n + 1 + d) m)) hfac
    simp only [T.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [htrans] at h
    exact h
  rw [ht, ← ha n m, LinearEquiv.symm_apply_apply, ← ha (n + 1) m,
    LinearEquiv.symm_apply_apply]
  rfl

end AlgebraicGeometry
