/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormallyUnramifiedConormal
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenRestriction

/-!
# Conormal vanishing on an open subscheme mapping isomorphically to the base

Source: Stacks Project, Tags 04FA and 04FF.
(blueprint: lem-weil-pbc-open-iso-conormal-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem universal_thickening_isIso_of_isIso
    {Z S Z' : Scheme.{u}} (h : Z ⟶ S) [IsIso h]
    (i : Z ⟶ Z') (s : Z' ⟶ S) (H : IsUniversalFirstOrderThickening h i s) :
    IsIso i := by
  let r := s ≫ inv h
  have hir : i ≫ r = 𝟙 Z := by simp [r, ← Category.assoc, H.2.1]
  have hself := H.2.2 i s (𝟙 Z) H.1 (by simpa using H.2.1)
  have hri : r ≫ i = 𝟙 Z' := by
    apply hself.unique
    · constructor
      · simp [r, Category.assoc, H.2.1]
      · simp [← Category.assoc, hir]
    · simp
  exact ⟨r, hir, hri⟩

private theorem isZero_ideal_toModules_of_isIso {Z : Scheme.{u}}
    (J : Z.IdealSheafData) [IsIso J.subschemeι] : IsZero J.toModules := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  change m = 0
  apply J.injective_toModulesι_app U.unop
  have hm : J.subschemeι.app U.unop (J.toModulesι.app U.unop m) = 0 := by
    exact (J.range_toModulesι_app_eq U.unop).le ⟨m, rfl⟩
  exact (ConcreteCategory.bijective_of_isIso (J.subschemeι.app U.unop)).injective
    (hm.trans (map_zero _).symm) |>.trans (map_zero _).symm

private theorem iso_conormal_isZero {Z S Z' : Scheme.{u}} (h : Z ⟶ S)
    [FormallyUnramified h] [IsIso h] (i : Z ⟶ Z') (s : Z' ⟶ S)
    (H : IsUniversalFirstOrderThickening h i s) :
    IsZero (formallyUnramifiedConormal h i s H) := by
  have : IsIso i := universal_thickening_isIso_of_isIso h i s H
  have : IsIso i.ker.subschemeι := by
    rw [i.ker_eq_bot_of_isIso]
    infer_instance
  let : (Scheme.Modules.tensorPullback i).IsLeftAdjoint :=
    ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction i⟩
  exact (Scheme.Modules.tensorPullback i).map_isZero
    (isZero_ideal_toModules_of_isIso i.ker)

/-- Restricting the universal conormal to an open subscheme on which the structure
morphism is an isomorphism gives a zero module. No flatness is needed.
Source: Stacks Project, Tag 04FA and the calculation C_{X/X} = 0 in Tag 04FF.
(blueprint: lem-weil-pbc-open-iso-conormal-zero).
Proof: let V be the open image of j and identify T with V by the open immersion
isomorphism. Apply universalFirstOrderThickening_open_restriction with V and the
whole base S. It identifies the restriction of C_h with the universal conormal of
the restricted morphism V -> S, which is an isomorphism since j followed by h is.
For an isomorphism e:V -> S, the map from the ambient thickening back to V is
its structure map followed by the inverse of e. One composite is the identity by
the compatibility equation; the other is the identity by universal uniqueness,
applied to the thickening itself. Thus the thickening immersion is an isomorphism
and its kernel ideal is zero. The ideal module is zero: its inclusion is injective
on every open, and every section in its image is killed by the isomorphism from
the ambient scheme to the closed subscheme. Tensor pullback preserves zero objects
as a left adjoint, so the restricted conormal is zero.
Finally open-immersion tensor pullback agrees with restriction, and pullback along
the isomorphism T -> V preserves zero objects, as a left adjoint. This includes the
empty open subscheme and imposes no finite type assumption. -/
theorem open_iso_conormal_isZero {Z S Z' T : Scheme.{u}} (h : Z ⟶ S)
    [FormallyUnramified h] (i : Z ⟶ Z') (s : Z' ⟶ S)
    (H : IsUniversalFirstOrderThickening h i s)
    (j : T ⟶ Z) [IsOpenImmersion j] [IsIso (j ≫ h)] :
    IsZero ((Scheme.Modules.tensorPullback j).obj
      (formallyUnramifiedConormal h i s H)) := by
  let V := j.opensRange
  have hVU : V ≤ h ⁻¹ᵁ (⊤ : S.Opens) := by simp
  obtain ⟨hV, hVeq, _, V', iV, sV, _, _, _, _, _, _, hVform, HV, ⟨e⟩⟩ :=
    universalFirstOrderThickening_open_restriction h i s H
      (inferInstance : FormallyUnramified h) V ⊤ hVU
  have : IsIso (⊤ : S.Opens).ι := inferInstanceAs (IsIso S.topIso.hom)
  have hfac : hV ≫ (⊤ : S.Opens).ι = j.isoOpensRange.inv ≫ (j ≫ h) := by
    rw [← hVeq, ← Category.assoc, j.isoOpensRange_inv_comp]
  have : IsIso (hV ≫ (⊤ : S.Opens).ι) := by rw [hfac]; infer_instance
  have : IsIso hV := IsIso.of_isIso_comp_right hV (⊤ : S.Opens).ι
  let := hVform
  have hz := (iso_conormal_isZero hV iV sV HV).of_iso e
  let a : Scheme.Modules.tensorPullback V.ι ≅ Scheme.Modules.restrictFunctor V.ι :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction V.ι).some.leftAdjointUniq
      (Scheme.Modules.restrictAdjunction V.ι)
  have hz' := hz.of_iso (a.app (formallyUnramifiedConormal h i s H))
  let : (Scheme.Modules.tensorPullback j.isoOpensRange.hom).IsLeftAdjoint :=
    ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction j.isoOpensRange.hom⟩
  have hz'' := (Scheme.Modules.tensorPullback j.isoOpensRange.hom).map_isZero hz'
  obtain ⟨b⟩ := Scheme.Modules.nonempty_tensorPullbackComp j.isoOpensRange.hom V.ι
  have hzcomp := hz''.of_iso (b.app (formallyUnramifiedConormal h i s H))
  change IsZero ((Scheme.Modules.tensorPullback
    (j.isoOpensRange.hom ≫ j.opensRange.ι)).obj _) at hzcomp
  simpa only [j.isoOpensRange_hom_ι] using hzcomp

end AlgebraicGeometry
