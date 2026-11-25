/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-! # Sections of ample powers in an ideal sheaf

Source: Stacks Project, Properties, Proposition 01Q3, equivalence of (1) and (6)
(blueprint: lem-sc-ample-ideal-section).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- If a point is outside a quasi-coherent ideal sheaf on a quasi-compact scheme, an
ample power has a global section coming from that ideal and nonvanishing at the point.
Source: Stacks Project, Properties, Proposition 01Q3, equivalence of (1) and (6)
(blueprint: lem-sc-ample-ideal-section).

Proof: choose an affine nonvanishing neighbourhood from ampleness, choose a section of the
ideal which is a unit at the point, clear its denominator using the section defining that
neighbourhood, and multiply once more by that section to ensure a positive tensor power.
The resulting section lies in the image of the ideal inclusion tensored with the power and
is nonvanishing at the chosen point.
-/
theorem exists_section_of_ample_ideal
    {Y : Scheme.{u}} [CompactSpace Y] (M : Y.Modules) [M.IsInvertible]
    (hM : Scheme.Modules.IsAmple Y M) (J : Y.IdealSheafData)
    {y : Y} (hy : y ∉ (J.support : Set Y)) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Γ(M.tensorPow n, ⊤),
      ∃ v : Γ(J.toModules.tensorObj (M.tensorPow n), ⊤),
        u = ((tensorHom J.toModulesι (𝟙 (M.tensorPow n)) ≫
          (MonoidalCategory.leftUnitor (M.tensorPow n)).hom).app ⊤) v ∧
      y ∈ Scheme.Modules.nonvanishingLocus (M.tensorPow n) u := by
  classical
  obtain ⟨d, hd, s, U, hyU, hUa, hU⟩ := hM.2 y
  let L := M.tensorPow d
  let σ : 𝟙_ Y.Modules ⟶ L := homOfGlobalSection L s
  have : L.IsInvertible := inferInstance
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  have hσ : σ.app ⊤ (unitSectionsEquiv ⊤ 1) = s := by
    exact (homOfGlobalSection_app_one L s ⊤).trans (Scheme.Modules.presheaf_map_id_apply _ _)
  have hUs : U = (Hom.zeroLocus σ).support.compl := by
    ext x
    change x ∈ U ↔ x ∈ (Hom.zeroLocus σ).support.compl
    rw [hU x, ← generatesAt_iff_mem_compl_support σ x, hσ]
    exact mem_nonvanishingLocus_iff_generatesAt L s x
  have he : IsFreeGenerator (σ.app U (unitSectionsEquiv U 1)) :=
    isFreeGenerator_app_one_of_le σ hUs.le
  have hyJ : y ∉ Y.zeroLocus (J.ideal ⟨U, hUa⟩ : Set Γ(Y, U)) := by
    exact fun h ↦ hy ((J.mem_support_iff_of_mem (U := ⟨U, hUa⟩) hyU).mpr h)
  rw [Y.mem_zeroLocus_iff] at hyJ
  push Not at hyJ
  obtain ⟨a, haJ, hya⟩ := hyJ
  obtain ⟨t, ht⟩ := (J.range_toModulesι_app ⟨U, hUa⟩).superset haJ
  have : Y.IsSeparated := isSeparated_of_isAmple Y M hM
  have : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) J.toModules :=
    by
      have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
      have := SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
      have : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf)
          ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
            (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
        isQuasicoherent_pushforward_of_isClosedImmersion J.subschemeι _
      exact isQuasicoherent_kernel J.toPushforwardSubscheme
  let t' : Γ(J.toModules, (Hom.zeroLocus σ).support.compl) := hUs ▸ t
  obtain ⟨m, v, hv⟩ := exists_tensorPowSection_eq_restrict
    (Limits.terminal.from Y) L σ J.toModules t'
  have hvU : (J.toModules ⊗ L.tensorPow m).presheaf.map (homOfLE le_top).op v =
      tmulSection t (tensorPowSectionOne σ m U) := by
    have hh := hv
    rw [rightUnitor_inv_comp_whiskerLeft_app] at hh
    subst U
    exact hh
  let w := (mulTensorPowSection σ J.toModules m 1).app ⊤ v
  have hw : (J.toModules ⊗ L.tensorPow (m + 1)).presheaf.map
      (homOfLE le_top).op w = tmulSection t (tensorPowSectionOne σ (m + 1) U) := by
    rw [← Hom.app_presheaf_map, hvU, mulTensorPowSection_app_tmulSection]
  let e : L.tensorPow (m + 1) ≅ M.tensorPow (d * (m + 1)) :=
    (M.tensorPowMulIso d (m + 1)).symm
  let v' := (J.toModules ◁ e.hom).app ⊤ w
  let μ : J.toModules ⊗ M.tensorPow (d * (m + 1)) ⟶ M.tensorPow (d * (m + 1)) :=
    tensorHom J.toModulesι (𝟙 _) ≫ (λ_ _).hom
  let u := μ.app ⊤ v'
  refine ⟨d * (m + 1), Nat.mul_pos hd (Nat.succ_pos m), u, v', rfl, ?_⟩
  apply (mem_nonvanishingLocus_iff_generatesAt _ u y).mpr
  have hu : (M.tensorPow (d * (m + 1))).presheaf.map (homOfLE le_top).op u =
      a • e.hom.app U (tensorPowSectionOne σ (m + 1) U) := by
    dsimp only [u, v']
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map, hw,
      whiskerLeft_app_tmulSection]
    dsimp only [μ]
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection]
    erw [leftUnitor_hom_app_tmulSection']
    rw [ht]
    rfl
  exact generatesAt_of_mem_basicOpen
    ((isFreeGenerator_tensorPowSectionOne σ he (m + 1)).app_hom e) hu hya

end AlgebraicGeometry.Scheme.IdealSheafData
