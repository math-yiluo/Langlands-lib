/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
import all WeilConjectures.AlgebraicGeometry.FormallyUnramifiedConormal
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Kernel ideal modules under open restriction

Source: Stacks Project, Sheaves, Lemma 00A0; More on Morphisms, Lemma 09ZU;
and Morphisms, Section 01R1 preceding Definition 01R2.
(blueprint: lem-weil-pbc-open-restriction-kernel-module).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem open_kernel_zero_iff
    {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    {V : Z.Opens} {V' : Z'.Opens} (iV : V.toScheme ⟶ V'.toScheme)
    (hpre : i ⁻¹ᵁ V' = V) (hcomm : iV ≫ V'.ι = V.ι ≫ i)
    (W : V'.toScheme.Opens) (x : Γ(Z', V'.ι ''ᵁ W)) :
    iV.app W ((V'.ι.appIso W).hom x) = 0 ↔ i.app (V'.ι ''ᵁ W) x = 0 := by
  have hle : i ⁻¹ᵁ (V'.ι ''ᵁ W) ≤ V.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι, ← hpre]
    apply i.preimage_mono
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have : IsIso (V.ι.app (i ⁻¹ᵁ (V'.ι ''ᵁ W))) := V.ι.isIso_app _ hle
  rw [IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq iV V'.ι
    (V.ι ≫ i) hcomm.symm W]
  simp only [CommRingCat.comp_apply, Iso.hom_inv_id_apply]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1]
  rw [Scheme.Hom.comp_app]
  simp only [CommRingCat.comp_apply]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The kernel ideal module of a closed immersion restricts to the kernel ideal
module of its restriction to an ambient open subscheme.
Source: Stacks Project, Sheaves, Lemma 00A0; More on Morphisms, Lemma 09ZU;
and Morphisms, Section 01R1 preceding Definition 01R2.
(blueprint: lem-weil-pbc-open-restriction-kernel-module).
Proof: The preimage equality and commuting square identify `iV` with the base
change of `i` along `V'.ι`. On every open of `V'`, its functions are the functions
on the corresponding ambient open, and the functions on its inverse image in
`V` are those on the inverse image in `Z`. These identifications commute with
the two immersion maps. Their kernels therefore agree. The ideal modules are
the kernels of the structure module maps to the closed subschemes; the section
identifications commute with restriction and scalar multiplication, giving an
isomorphism of ideal modules. Finally tensor pullback along the open immersion
is restriction, by uniqueness of its left adjoint to pushforward. -/
theorem nonempty_tensorPullback_open_kernel
    {Z Z' : Scheme.{u}} (i : Z ⟶ Z') [IsClosedImmersion i]
    {V : Z.Opens} {V' : Z'.Opens} (iV : V.toScheme ⟶ V'.toScheme)
    [IsClosedImmersion iV] (hpre : i ⁻¹ᵁ V' = V)
    (hcomm : iV ≫ V'.ι = V.ι ≫ i) :
    Nonempty ((Scheme.Modules.tensorPullback V'.ι).obj i.ker.toModules ≅
      iV.ker.toModules) := by
  classical
  let M := (Scheme.Modules.restrictFunctor V'.ι).obj i.ker.toModules
  let α : M ⟶ SheafOfModules.unit V'.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctor V'.ι).map i.ker.toModulesι ≫
      (Scheme.Modules.restrictUnitIso V'.ι).hom
  have hα (W : V'.toScheme.Opens) (s : Γ(M, W)) :
      α.app W s = (V'.ι.appIso W).hom (i.ker.toModulesι.app (V'.ι ''ᵁ W) s) := rfl
  have hzero : α ≫ iV.ker.toPushforwardSubscheme = 0 := by
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    change iV.ker.subschemeι.app W (α.app W s) = 0
    have hs : i.app (V'.ι ''ᵁ W) (i.ker.toModulesι.app (V'.ι ''ᵁ W) s) = 0 := by
      have hm : i.ker.toModulesι.app (V'.ι ''ᵁ W) s ∈
          Set.range (i.ker.toModulesι.app (V'.ι ''ᵁ W)) := ⟨s, rfl⟩
      rwa [range_kernelIdeal] at hm
    have hm : α.app W s ∈ Set.range (iV.ker.toModulesι.app W) := by
      rw [range_kernelIdeal]
      change iV.app W (α.app W s) = 0
      rw [hα]
      exact (open_kernel_zero_iff i iV hpre hcomm W _).mpr hs
    rwa [Scheme.IdealSheafData.range_toModulesι_app_eq] at hm
  let δ : M ⟶ iV.ker.toModules := kernel.lift _ α hzero
  have hδ : δ ≫ iV.ker.toModulesι = α := kernel.lift_ι _ _ _
  have hδapp (W : V'.toScheme.Opens) (s : Γ(M, W)) :
      iV.ker.toModulesι.app W (δ.app W s) = α.app W s :=
    congrArg (fun f ↦ f.app W s) hδ
  have : IsIso δ := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro s t he
      apply i.ker.injective_toModulesι_app (V'.ι ''ᵁ W)
      apply (ConcreteCategory.bijective_of_isIso (V'.ι.appIso W).hom).1
      rw [← hα W s, ← hα W t, ← hδapp W s, ← hδapp W t, he]
    · intro t
      let x := (V'.ι.appIso W).inv (iV.ker.toModulesι.app W t)
      have hx : i.app (V'.ι ''ᵁ W) x = 0 := by
        apply (open_kernel_zero_iff i iV hpre hcomm W x).mp
        simp only [x, Iso.inv_hom_id_apply]
        have hm : iV.ker.toModulesι.app W t ∈ Set.range (iV.ker.toModulesι.app W) :=
          ⟨t, rfl⟩
        rwa [range_kernelIdeal] at hm
      have hm : x ∈ Set.range (i.ker.toModulesι.app (V'.ι ''ᵁ W)) := by
        rwa [range_kernelIdeal]
      obtain ⟨s, hs⟩ := hm
      refine ⟨s, ?_⟩
      apply iV.ker.injective_toModulesι_app W
      rw [hδapp, hα, hs]
      exact Iso.inv_hom_id_apply _ _
  let e :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction V'.ι)).leftAdjointUniq
      (Scheme.Modules.restrictAdjunction V'.ι)
  exact ⟨e.app _ ≪≫ asIso δ⟩

end AlgebraicGeometry
