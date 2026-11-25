/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- An ideal-power-annihilated quasi-coherent module remains annihilated by the
inverse image ideal after closed pushforward and any module isomorphism.
Source: Stacks Project, proof of Theorem 088E and Tags 01Y9, 01I8.
(blueprint: aux-closed-immersion-ideal-power-annihilation)

Proof: On each affine open U of X its inverse image V is affine. The ideal of
(L^t).map j on U is the inverse image of L(V)^t under the structure ring map.
The affine zero-product criterion turns the hypothesis into annihilation of F(V).
Pushforward uses the same section group with the restricted scalar action. The
isomorphism e is linear on sections, so transfers this annihilation to H(U).
The affine product-section formula makes the image of the product inclusion zero.
The inclusion is injective on sections, hence the product has zero sections on each
affine open and is the zero sheaf. This also covers t = 0 and empty schemes. -/
theorem closedImmersion_idealPower_annihilation
    {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    (L : Z.IdealSheafData) (t : ℕ) (F : Z.Modules) [F.IsQuasicoherent]
    (H : X.Modules) [H.IsQuasicoherent]
    (e : H ≅ (Modules.pushforward j).obj F)
    (hkill : IsZero (idealModuleProduct (idealSheafPower L.toModulesι t).2 F)) :
    IsZero (idealModuleProduct ((L ^ t).map j).toModulesι H) := by
  have hcover : ∀ x : Z, ∃ U ∈ (Set.univ : Set Z.affineOpens), x ∈ U.1 := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : Z.Opens) from trivial)
        (⊤ : Z.Opens).2
    exact ⟨⟨U, hU⟩, Set.mem_univ _, hx⟩
  have hk := (idealPowerProduct_isZero_iff_affine_cover Z F L Set.univ hcover t).mp hkill
  let J := (L ^ t).map j
  have hann (U : X.affineOpens) :
      J.ideal U ≤ Module.annihilator Γ(X, U.1) Γ(H, U.1) := by
    intro a ha
    have ha' : (j.app U.1).hom a ∈ L.ideal ⟨j ⁻¹ᵁ U.1, U.2.preimage j⟩ ^ t := by
      simpa [J, IdealSheafData.ideal_map_of_isAffineHom, IdealSheafData.ideal_pow]
        using ha
    apply Module.mem_annihilator.mpr
    intro s
    apply (Modules.appLinearEquivOfIso e U.1).injective
    rw [map_smul, map_zero]
    exact Module.mem_annihilator.mp
      (hk ⟨j ⁻¹ᵁ U.1, U.2.preimage j⟩ (Set.mem_univ _) ha') _
  apply Modules.isZero_of_forall_affineOpens
  intro U
  let ι := idealModuleProductι J.toModulesι H
  have : Mono ι := by
    dsimp [ι, idealModuleProductι]
    infer_instance
  have hinj : Function.Injective (ι.app U.1) := by
    exact (ModuleCat.mono_iff_injective _).mp
      ((SheafOfModules.evaluation _ (op U.1)).map_mono _)
  have hz : J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(H, U.1)) ≤ ⊥ := by
    apply Submodule.smul_le.mpr
    intro a ha s _
    simpa using Module.mem_annihilator.mp (hann U ha) s
  have hzero (s : Γ(idealModuleProduct J.toModulesι H, U.1)) : ι.app U.1 s = 0 := by
    have hm : ι.app U.1 s ∈ J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(H, U.1)) := by
      exact (Set.ext_iff.mp ((Modules.ideal_times_quasiCoherent_affine_sections J H).2.2.2.1
        U).1 _).mp ⟨s, rfl⟩
    simpa using hz hm
  exact ⟨fun a b ↦ hinj (by rw [hzero a, hzero b])⟩

end AlgebraicGeometry.Scheme
