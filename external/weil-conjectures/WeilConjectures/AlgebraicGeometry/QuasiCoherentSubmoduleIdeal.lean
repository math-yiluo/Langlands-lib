/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-!
# Quasi-coherent submodules of the structure sheaf are ideal sheaves

Source: Stacks Project, Tag 01XF, coordinate-filtration paragraph;
Mathlib's `Scheme.IdealSheafData` and `range_toModulesι_app`
(blueprint: lem-pqf-quasi-coherent-submodule-ideal).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-coherent submodule of the structure sheaf is isomorphic to the module
of ideal sheaf data.

Source: Stacks Project, Tag 01XF, coordinate-filtration paragraph
(blueprint: lem-pqf-quasi-coherent-submodule-ideal).

Proof: On each affine open U take J(U) to be the range of the injective linear map
on sections induced by i. It is a submodule of the section ring acting on itself,
hence an ideal. Quasi-coherence identifies restriction to each principal open D(f)
with localization. Thus J(D(f)) is the image ideal of J(U) under ring restriction.
These ideals and their localization equalities construct Scheme.IdealSheafData J,
using its default support (the intersection of their zero loci). The inclusion
J.toModulesι has section range J(U) on every affine open by range_toModulesι_app.
Every section in the image of i on an affine open is killed by the closed-subscheme
restriction map, by idealOfOpens_eq_ideal and mem_idealOfOpens_iff. The sheaf condition
extends this vanishing to all opens. Hence i lifts to a morphism M → J.toModules by
the kernel universal property. On every affine open this lift is injective because
i is injective, and surjective because the two inclusions have equal ranges.
The affine-basis isomorphism criterion makes the lift an isomorphism. Transport the
quasi-coherence of M along it. For a zero submodule the ideals are zero; for the
identity inclusion they are unit ideals. The argument does not require the scheme
to be affine or quasi-compact, nor the module to be finitely generated.
-/
theorem quasiCoherent_submodule_ideal (X : Scheme.{u}) {M : X.Modules}
    [M.IsQuasicoherent] (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono i] :
    ∃ J : X.IdealSheafData, J.toModules.IsQuasicoherent ∧
      Nonempty (M ≅ J.toModules) := by
  classical
  let ideals (U : X.affineOpens) : Ideal Γ(X, U.1) :=
    LinearMap.range (Scheme.Modules.Hom.appₗ i U.1)
  have hlocal (U : X.affineOpens) (f : Γ(X, U.1)) :
      (ideals U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
        ideals (X.affineBasicOpen f) := by
    let ρ := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      rintro x ⟨m, rfl⟩
      refine ⟨M.presheaf.map (homOfLE (X.basicOpen_le f)).op m, ?_⟩
      exact Scheme.Modules.Hom.app_presheaf_map i (homOfLE (X.basicOpen_le f)) m
    · rintro y ⟨m, rfl⟩
      obtain ⟨n, a, ha⟩ :=
        Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen M U.2 f m
      have hx : ρ (i.app U.1 a) ∈ (ideals U).map ρ.hom :=
        Ideal.mem_map_of_mem _ ⟨a, rfl⟩
      have he : ρ (i.app U.1 a) = ρ f ^ n • i.app (X.basicOpen f) m := by
        calc
          ρ (i.app U.1 a) = i.app (X.basicOpen f)
              (M.presheaf.map (homOfLE (X.basicOpen_le f)).op a) :=
            (Scheme.Modules.Hom.app_presheaf_map i
              (homOfLE (X.basicOpen_le f)) a).symm
          _ = ρ f ^ n • i.app (X.basicOpen f) m := by
            rw [ha, Scheme.Modules.Hom.app_smul]
      rw [he] at hx
      change ρ f ^ n * _ ∈ (ideals U).map ρ.hom at hx
      exact ((ideals U).map ρ.hom).unit_mul_mem_iff_mem
        ((X.toRingedSpace.isUnit_res_basicOpen f).pow n) |>.mp hx
  let J : X.IdealSheafData := { ideal := ideals, map_ideal_basicOpen := hlocal }
  have hz_affine (U : X.affineOpens) (m : Γ(M, U.1)) :
      J.subschemeι.app U.1 (i.app U.1 m) = 0 := by
    apply (J.mem_idealOfOpens_iff).mp
    rw [J.idealOfOpens_eq_ideal]
    exact ⟨m, rfl⟩
  have hz : i ≫ J.toPushforwardSubscheme = 0 := by
    apply Scheme.Modules.hom_ext
    intro U
    ext m
    let N : X.Modules := (SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit J.subscheme.ringCatSheaf)
    change (i ≫ J.toPushforwardSubscheme).app U m = (0 : Γ(N, U))
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
      (fun V : {V : X.affineOpens // V.1 ≤ U} ↦ V.1.1) U
      (fun V ↦ homOfLE V.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
      exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
    · intro V
      rw [← Scheme.Modules.Hom.app_presheaf_map, map_zero]
      exact hz_affine V.1 (M.presheaf.map (homOfLE V.2).op m)
  let l : M ⟶ J.toModules := kernel.lift J.toPushforwardSubscheme i hz
  have hl : l ≫ J.toModulesι = i := kernel.lift_ι _ _ _
  have hinj (U : X.Opens) : Function.Injective (i.app U) :=
    (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map i)).mp inferInstance
  have hli (U : X.Opens) (m : Γ(M, U)) : J.toModulesι.app U (l.app U m) = i.app U m := by
    have h := congrArg (fun a ↦ a.app U m) hl
    exact h
  have : IsIso l := Scheme.Modules.isIso_of_bijective_app_of_isAffineOpen l fun U hU ↦ by
    constructor
    · intro x y hxy
      apply hinj U
      rw [← hli U x, ← hli U y, hxy]
    · intro y
      have hy : J.toModulesι.app U y ∈ ideals ⟨U, hU⟩ := by
        change J.toModulesι.app U y ∈ (J.ideal ⟨U, hU⟩ : Set Γ(X, U))
        rw [← J.range_toModulesι_app ⟨U, hU⟩]
        exact ⟨y, rfl⟩
      obtain ⟨m, hm⟩ := hy
      refine ⟨m, J.injective_toModulesι_app U ?_⟩
      exact (hli U m).trans hm
  refine ⟨J, ?_, ⟨asIso l⟩⟩
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (asIso l) inferInstance

end AlgebraicGeometry
