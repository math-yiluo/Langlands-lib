/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.AlgebraicGeometry.CoherentFormalKernelComponentAffineAnnihilation
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Annihilation of kernels and cokernels of coherent formal module maps -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An intermediate kernel-annihilation component of the affine-cover reduction.
Source: Stacks, Remark 0888 (blueprint: lem-weil-pbc-formal-systems-annihilated-by-power-kernel).
The proof is the corresponding kernel/cokernel half of the finite affine-cover
argument. The finite affine cover is reduced modulo each power of the ideal, the
commutative-algebra annihilation lemma is applied, and local annihilation is glued
over the affine cover.
-/
theorem coherentFormalModule_annihilated_double_kernel (X : Scheme.{u}) [IsNoetherian X]
    (I K : X.IdealSheafData) (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (r : ℕ) (U : Fin r → X.affineOpens) (t : ℕ)
    (hcover : (⨆ i, (U i).1) = ⊤) (ht : 1 ≤ t)
    (h : ∀ i : Fin r,
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom) ∧
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)) :
          ModuleCat Γ(X, (U i).1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom)) :
    ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (kernel (α.hom.app (op n)))) := by
  intro n
  let : (F.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (F.property.1 n)).1
  let : (G.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (G.property.1 n)).1
  let : (kernel (α.hom.app (op n))).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_kernel (α.hom.app (op n))
  let S : Set X.affineOpens := Set.range U
  have hS : ∀ x : X, ∃ V ∈ S, x ∈ V.1 := by
    intro x
    have hx : x ∈ (⨆ i, (U i).1) := by simp [hcover]
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U i, ⟨i, rfl⟩, hi⟩
  apply (Scheme.idealPowerProduct_isZero_iff_affine_cover X
    (kernel (α.hom.app (op n))) K S hS (2 * t)).mpr
  rintro V ⟨i, rfl⟩
  exact coherentFormalModule_kernel_component_affine_annihilation
    X I K F G α (U i) t ht (h i) n

end AlgebraicGeometry
