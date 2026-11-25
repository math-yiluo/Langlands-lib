/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.CoherentIdealPowerStableAnnihilator
import WeilConjectures.AlgebraicGeometry.CoherentIdealProductIntersectionBound
import WeilConjectures.AlgebraicGeometry.IdealPowerComplement
import WeilConjectures.AlgebraicGeometry.IdealDataRecursivePowerComparison
import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Removing ideal-power torsion from a coherent module

Source: Stacks Project, Tag 01YB, second paragraph of the proof.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

private theorem product_qc {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [K.IsQuasicoherent] [M.IsQuasicoherent] :
    (idealModuleProduct i M).IsQuasicoherent := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have := (quasiCoherent_tensor_product_affine_sections K M).1
  let a := MonoidalCategory.whiskerRight i M ≫ (MonoidalCategory.leftUnitor M).hom
  have hi := (quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.1
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage a) hi

local instance {X : Scheme.{u}} (H : X.Modules)
    {V W : X.Opens} (h : V ≤ W) :
    SMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op V))
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (H.val.obj (op V))) :=
  inferInstanceAs (SMul (X.sheaf.obj.obj (op V)) (H.val.obj (op V)))

/-- A sufficiently high ideal-power product has no ideal-power torsion,
and its inclusion is bijective on sections over the ideal complement.

Source: Stacks Project, Tag 01YB, second paragraph; Tags 01Y8 and 01YA.
(blueprint: lem-pc-coherent-ideal-power-torsion-free-product)

Proof: The quasi-coherent annihilator submodules H_n of I^n form an increasing
chain in H. Noetherian ACC gives r with every H_n contained in T=H_r.
Artin-Rees gives c with I^(r+c)H intersect T contained in I^r T=0.
Take k=r+c and P=I^k H, the actual image of multiplication, not a chosen
existence witness. Ideal products are quasi-coherent. The inclusion P into H
is mono because it is an image inclusion. On the complement I is the unit
ideal, so P restricts to H and the inclusion is bijective on U-sections.
For a section x of P killed locally by I^n, its image in H belongs to H_n
and therefore to T. It also belongs to P; the zero intersection forces its
image to vanish. The mono inclusion is injective on sections, so x=0.
The affine power formula identifies recursive powers with I^n, including
n=0 where annihilation by the unit already forces zero. The same argument
covers empty U, the unit ideal, and the zero module. -/
theorem exists_coherent_idealPower_torsionFree_product
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (H : X.Modules) [H.IsQuasicoherent]
    (hH : RingedSpace.IsCoherent X.toRingedSpace H) (U : X.Opens)
    (hI : (I.support : Set X) = (U : Set X)ᶜ) :
    ∃ k : ℕ,
      let P := idealModuleProduct (idealSheafPower I.toModulesι k).2 H
      let j := idealModuleProductι (idealSheafPower I.toModulesι k).2 H
      P.IsQuasicoherent ∧ Mono j ∧ Function.Bijective (j.val.app (op U)) ∧
      ∀ (n : ℕ) (W : X.Opens) (x : P.val.obj (op W)),
        (∀ (V : X.Opens) (h : V ≤ W)
          (b : (idealSheafPower I.toModulesι n).1.val.obj (op V)),
          ((idealSheafPower I.toModulesι n).2.val.app (op V) b : Γ(X, V)) •
            P.val.map (homOfLE h).op x = 0) → x = 0 := by
  classical
  have : I.toModules.IsQuasicoherent := by
    simpa only [pow_one] using (idealData_recursive_power_comparison I 1).1
  have : I.toModules.IsFiniteType :=
    I.isFiniteType_toModules I.ofFiniteType_of_isLocallyNoetherian
  obtain ⟨V, hV, hbij⟩ := ideal_power_complement I.toModulesι
  have hsupport := (quasi_coherent_ideal_zero_set_affine X I).2.2.2.2
    I.subscheme I.subschemeι I.ker_subschemeι
  have hUV : U ≤ V := by
    intro x hx
    apply (hV x).mpr
    by_contra hn
    have hs : x ∈ (I.support : Set X) := by
      rw [← I.range_subschemeι, hsupport]
      exact hn
    rw [hI] at hs
    exact hs hx
  obtain ⟨r, T, a, hmono, hqc, hTzero, hmem⟩ :=
    exists_coherent_idealPower_stable_annihilator I H hH
  have : Mono a := hmono
  obtain ⟨k, hc⟩ := coherent_ideal_product_intersection_bound I H T hH a hqc r
  let P := idealModuleProduct (idealSheafPower I.toModulesι k).2 H
  let j := idealModuleProductι (idealSheafPower I.toModulesι k).2 H
  have hpqc : (idealSheafPower I.toModulesι k).1.IsQuasicoherent := by
    obtain ⟨hq, e, _⟩ := idealData_recursive_power_comparison I k
    have := hq
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance
  have : Mono j := by dsimp [j, idealModuleProductι]; infer_instance
  refine ⟨k, product_qc _ H, inferInstance, ?_, ?_⟩
  · have hi : Function.Injective (j.val.app (op U)) :=
      (ModuleCat.mono_iff_injective _).mp
        ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map_mono j)
    refine ⟨hi, ?_⟩
    intro x
    obtain ⟨b, hb⟩ := (hbij k U hUV).2 (1 : Γ(X, U))
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let μ := MonoidalCategory.whiskerRight (idealSheafPower I.toModulesι k).2 H ≫
      (MonoidalCategory.leftUnitor H).hom
    refine ⟨(Limits.factorThruImage μ).app U (tmulSection b x), ?_⟩
    change (Limits.factorThruImage μ ≫ Limits.image.ι μ).app U (tmulSection b x) = x
    rw [Limits.image.fac]
    change (MonoidalCategory.leftUnitor H).hom.app U
      ((MonoidalCategory.whiskerRight (idealSheafPower I.toModulesι k).2 H).app U
        (tmulSection b x)) = x
    rw [whiskerRight_app_tmulSection, leftUnitor_hom_app_tmulSection', hb]
    change (1 : Γ(X, U)) • x = x
    exact one_smul _ _
  · intro n W x hx
    have hjx : j.app W x ∈ Set.range (a.app W) := by
      apply hmem n W (j.app W x)
      intro W' h b
      change (show Γ(X, W') from (idealSheafPower I.toModulesι n).2.app W' b) •
        H.presheaf.map (homOfLE h).op (j.app W x) = 0
      rw [← Hom.app_presheaf_map, ← Hom.app_smul]
      exact (congrArg (j.app W') (hx W' h b)).trans (map_zero _)
    have hz := hc W ⟨⟨x, rfl⟩, hjx⟩
    rw [hTzero, Limits.zero_comp] at hz
    obtain ⟨z, hz⟩ := hz
    have hi : Function.Injective (j.val.app (op W)) :=
      (ModuleCat.mono_iff_injective _).mp
        ((SheafOfModules.evaluation X.ringCatSheaf (op W)).map_mono j)
    apply hi
    change j.app W x = j.app W 0
    rw [map_zero]
    change (0 : Γ(H, W)) = j.app W x at hz
    exact hz.symm


end AlgebraicGeometry.Scheme.Modules
