/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleLimitAnnihilators
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineProjections
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Annihilation of formal kernels and cokernels on an affine cover

Source: Stacks Project, Lemmas 087W and 087X, and Remark 0888.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem formal_annihilation_iff_limit
    (X : Scheme.{u}) [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) (J : Type v) (U : J → X.affineOpens)
    (hcover : (⨆ j, (U j).1) = ⊤) (t : ℕ) :
    (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι t).2 (M.obj.obj (op n)))) ↔
    ∀ j : J, K.ideal (U j) ^ t ≤ Module.annihilator Γ(X, (U j).1)
      (limit (M.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)) :
        ModuleCat Γ(X, (U j).1)) := by
  have hS : ∀ x : X, ∃ V ∈ Set.range U, x ∈ V.1 := by
    intro x
    have hx : x ∈ (⨆ j, (U j).1) := by rw [hcover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U j, ⟨j, rfl⟩, hj⟩
  have qc (n : ℕ) : (M.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (M.property.1 n)).1
  have level (n : ℕ) :
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (M.obj.obj (op n))) ↔
      ∀ j : J, K.ideal (U j) ^ t ≤
        Module.annihilator Γ(X, (U j).1) Γ(M.obj.obj (op n), (U j).1) := by
    have := qc n
    rw [Scheme.idealPowerProduct_isZero_iff_affine_cover X _ K (Set.range U) hS t]
    exact ⟨fun h j ↦ h (U j) ⟨j, rfl⟩, fun h V ⟨j, hj⟩ ↦ hj ▸ h j⟩
  constructor
  · intro h j a ha
    apply Module.mem_annihilator.mpr
    intro x
    apply Concrete.limit_ext
      (M.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op (U j).1))
    intro n
    obtain ⟨n⟩ := n
    simpa only [map_smul, map_zero] using
      Module.mem_annihilator.mp ((level n).mp (h n) j ha)
        (limit.π (M.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op (U j).1))
          (op n) x)
  · intro h n
    apply (level n).mpr
    intro j a ha
    apply Module.mem_annihilator.mpr
    intro x
    obtain ⟨y, rfl⟩ := (coherentFormalModule_affine_projections X I M (U j) n).1 x
    simpa only [map_smul, map_zero] using congrArg
      (limit.π (M.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)) (op n))
      (Module.mem_annihilator.mp (h j ha) y)

/-- On any affine open cover, a fixed positive power kills a formal kernel and cokernel
exactly when its section ideals kill the kernels and cokernels of the affine limit maps.
Source: Stacks Project, Lemmas 087W and 087X (the affine description of the kernel)
(blueprint: lem-weil-pbc-formal-annihilation-kernel-cokernel-cover).

Proof:
1. The defining quotient isomorphisms give surjective transition maps on affine
   sections. Sequential inverse-limit surjectivity gives surjective projections.
2. The affine-cover ideal-product criterion detects each level's annihilation.
   Limit extensionality shows that annihilation at every level kills the limit;
   surjectivity of its projections proves the converse.
3. The affine-limit annihilator comparison identifies the limits of the formal
   kernel and cokernel with the linear kernel and cokernel for this test. Apply
   the equalities on each member of the cover and combine both conditions.
In particular the formal kernel is not asserted to be the termwise kernel.
For an empty index type covering X, X is empty and both sides hold. -/
theorem coherentFormalModule_annihilated_formal_cover
    (X : Scheme.{u}) [IsNoetherian X] (I K : X.IdealSheafData)
    (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (k : KernelFork α) (c : CokernelCofork α) (hk : IsLimit k) (hc : IsColimit c)
    (J : Type v) (U : J → X.affineOpens) (hcover : (⨆ j, (U j).1) = ⊤)
    (t : ℕ) (ht : 1 ≤ t) :
    (∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (k.pt.obj.obj (op n))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (c.pt.obj.obj (op n)))) ↔
    (∀ j : J,
      K.ideal (U j) ^ t ≤ Module.annihilator Γ(X, (U j).1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)))).hom) ∧
      K.ideal (U j) ^ t ≤ Module.annihilator Γ(X, (U j).1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)) :
          ModuleCat Γ(X, (U j).1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)))).hom)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have hk' := formal_annihilation_iff_limit X I K k.pt J U hcover (t + 1)
  have hc' := formal_annihilation_iff_limit X I K c.pt J U hcover (t + 1)
  constructor
  · intro h j
    have hkj := hk'.mp (fun n ↦ (h n).1) j
    have hcj := hc'.mp (fun n ↦ (h n).2) j
    obtain ⟨ek, ec⟩ := coherentFormalModule_limit_annihilators X I F G α k c hk hc (U j)
    exact ⟨ek ▸ hkj, ec ▸ hcj⟩
  · intro h
    have hkj : ∀ j, K.ideal (U j) ^ (t + 1) ≤ Module.annihilator Γ(X, (U j).1)
        (limit (k.pt.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)) :
          ModuleCat Γ(X, (U j).1)) := by
      intro j
      rw [(coherentFormalModule_limit_annihilators X I F G α k c hk hc (U j)).1]
      exact (h j).1
    have hcj : ∀ j, K.ideal (U j) ^ (t + 1) ≤ Module.annihilator Γ(X, (U j).1)
        (limit (c.pt.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)) :
          ModuleCat Γ(X, (U j).1)) := by
      intro j
      rw [(coherentFormalModule_limit_annihilators X I F G α k c hk hc (U j)).2]
      exact (h j).2
    exact fun n ↦ ⟨hk'.mpr hkj n, hc'.mpr hcj n⟩

end AlgebraicGeometry
