/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineProjections
import WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Affine sections of a component kernel are annihilated by the doubled ideal power.
Source: Stacks Project, Remark 0888
(blueprint: lem-weil-pbc-formal-systems-annihilated-kernel-affine-component).
The scalar quasi-inverses of the limit map preserve ideal multiples. Lift a section
of the component kernel to the limit, apply a scalar quasi-inverse to its image,
and project back. Products of two elements of K^t kill the section; these products
generate K^(2*t). Evaluation preserves kernels, so the kernel inclusion is injective. -/
theorem coherentFormalModule_kernel_component_affine_annihilation
    (X : Scheme.{u}) [IsNoetherian X]
    (I K : X.IdealSheafData) (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (V : X.affineOpens) (t : ℕ) (ht : 1 ≤ t)
    (h :
      K.ideal V ^ t ≤ Module.annihilator Γ(X, V.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op V.1)))).hom) ∧
      K.ideal V ^ t ≤ Module.annihilator Γ(X, V.1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op V.1)) :
          ModuleCat Γ(X, V.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op V.1)))).hom))
    (n : ℕ) :
    K.ideal V ^ (2 * t) ≤
      Module.annihilator Γ(X, V.1)
        Γ(kernel (α.hom.app (op n)), V.1) := by
  let E : X.Modules ⥤ ModuleCat Γ(X, V.1) := SheafOfModules.evaluation X.ringCatSheaf (op V.1)
  let p := (limit.π (F.obj ⋙ E) (op n)).hom
  let q := (limit.π (G.obj ⋙ E) (op n)).hom
  let a := (lim.map (Functor.whiskerRight α.hom E)).hom
  let b := (E.map (α.hom.app (op n))).hom
  let j := (E.map (kernel.ι (α.hom.app (op n)))).hom
  let J := I.ideal V ^ (n + 1)
  obtain ⟨hp, hkp⟩ := coherentFormalModule_affine_projections X I F V n
  obtain ⟨_, hkq⟩ := coherentFormalModule_affine_projections X I G V n
  change Function.Surjective p at hp
  change LinearMap.ker p = J • ⊤ at hkp
  change LinearMap.ker q = J • ⊤ at hkq
  have square (z : (limit (F.obj ⋙ E) : ModuleCat Γ(X, V.1))) : q (a z) = b (p z) := by
    exact ConcreteCategory.congr_hom (limMap_π (Functor.whiskerRight α.hom E) (op n)) z
  have hj (x : Γ(kernel (α.hom.app (op n)), V.1)) : b (j x) = 0 := by
    exact (Set.ext_iff.mp (Scheme.Modules.range_map_kernelι V.1
      (α.hom.app (op n))) (j x)).mp ⟨x, rfl⟩
  rw [two_mul, pow_add]
  refine Ideal.mul_le.mpr fun f hf g hg ↦ Module.mem_annihilator.mpr fun x ↦ ?_
  obtain ⟨z, hz⟩ := hp (j x)
  obtain ⟨k, _, hka, _, _⟩ :=
    ((LinearMap.ker_coker_annihilated_mod_ideal.{u, u, u, u, u, u, u}
      (K.ideal V) t ht a h.1 h.2).1 f g hf hg).2.2
  have haz : a z ∈ J • (⊤ : Submodule Γ(X, V.1) ((limit (G.obj ⋙ E) : ModuleCat Γ(X, V.1)))) := by
    rw [← hkq]
    exact LinearMap.mem_ker.mpr (by change q (a z) = 0; rw [square, hz, hj])
  have hkz : k (a z) ∈ J • (⊤ : Submodule Γ(X, V.1) ((limit (F.obj ⋙ E) : ModuleCat Γ(X, V.1)))) :=
    Submodule.smul_top_le_comap_smul_top J k haz
  have hfg : (f * g) • z ∈ LinearMap.ker p := by
    rw [hkp]
    have heq := LinearMap.congr_fun hka z
    change k (a z) = (f * g) • z at heq
    rwa [← heq]
  apply Scheme.Modules.injective_map_kernelι V.1 (α.hom.app (op n))
  change j ((f * g) • x) = j 0
  rw [j.map_smul, j.map_zero, ← hz, ← p.map_smul]
  exact LinearMap.mem_ker.mp hfg

end AlgebraicGeometry
