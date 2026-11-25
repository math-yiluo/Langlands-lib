/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.IdealPowerProductRestrictionZero
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Uniform annihilation on a finite cover -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Locally annihilated modules in the kernel and cokernel of a coherent map
have a common positive annihilating exponent on a Noetherian scheme.

Source: Stacks Project, Tag 0889(1), global torsion conclusion.
(blueprint: new-stage3-torsion-controlled-algebraization-descent-bound).

Proof: Quasi-compactness gives a finite subcover. Choose the supplied exponent on
each of its opens and take their maximum together with 1. If s is at least a
local exponent t, inclusion J^s into J^t makes the product at exponent s factor
through the zero product at exponent t. Restriction commutes with ideal products,
so the global products at exponent s restrict to zero on the finite subcover.
A sheaf that is zero on an open cover is zero, proving both conclusions. On the
empty scheme take s = 1; all modules are zero. If J = 0 the products already
vanish; if J is the unit ideal the hypotheses force both modules to vanish. -/
theorem torsionControlled_algebraization_descent_bound
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H F : CoherentModules X) (a : F ⟶ H)
    (ι : Type u) (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (hlocal : ∀ i, ∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2
          ((Scheme.Modules.restrictFunctor (U i).ι).obj (kernel a.hom))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2
          ((Scheme.Modules.restrictFunctor (U i).ι).obj (cokernel a.hom)))) :
      ∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a.hom)) := by
  classical
  choose t ht htk htc using hlocal
  have hU : Set.univ ⊆ ⋃ i, (U i : Set X) := by
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hU
  let s := max 1 (T.sup t)
  have hTcover : (⨆ i : {i // i ∈ T}, U i.val) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT (Set.mem_univ x))
    obtain ⟨hiT, hix⟩ := Set.mem_iUnion.mp hi
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hiT⟩, hix⟩
  have kill (M : X.Modules) [M.IsQuasicoherent]
      (hM : ∀ i, IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι (t i)).2
        ((Scheme.Modules.restrictFunctor (U i).ι).obj M))) :
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2 M) := by
    apply IsZero.of_mono_eq_zero (𝟙 _)
    apply Scheme.Modules.hom_eq_zero_of_restrict _ (fun i : {i // i ∈ T} ↦ U i.val) hTcover
    intro i
    rw [CategoryTheory.Functor.map_id]
    have hi : t i.val ≤ s := (Finset.le_sup i.property).trans (Nat.le_max_right _ _)
    obtain ⟨k, hk⟩ := formalModuleQuotient_factor (J.comap (U i.val).ι)
      (𝟙 ((Scheme.Modules.restrictFunctor (U i.val).ι).obj M)) hi
    have hz : IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i.val).ι).toModulesι s).2
        ((Scheme.Modules.restrictFunctor (U i.val).ι).obj M)) := by
      have : Mono (Scheme.idealModuleProductι
          (Scheme.idealSheafPower (J.comap (U i.val).ι).toModulesι s).2
          ((Scheme.Modules.restrictFunctor (U i.val).ι).obj M)) := by
        dsimp [Scheme.idealModuleProductι]
        infer_instance
      apply IsZero.of_mono_eq_zero (Scheme.idealModuleProductι _ _)
      simpa only [Category.comp_id, (hM i.val).eq_zero_of_tgt k, zero_comp] using hk
    exact ((Scheme.Modules.idealPowerProduct_restrict_isZero_iff
      J M (U i.val) s).mpr hz).eq_zero_of_src _
  have : F.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp F.property).1
  have : H.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp H.property).1
  have := Scheme.Modules.isQuasicoherent_kernel a.hom
  have := Scheme.Modules.isQuasicoherent_cokernel a.hom
  exact ⟨s, Nat.le_max_left _ _, kill (kernel a.hom) htk, kill (cokernel a.hom) htc⟩

end AlgebraicGeometry
