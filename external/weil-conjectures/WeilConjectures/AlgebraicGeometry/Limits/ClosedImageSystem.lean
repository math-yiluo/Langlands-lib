/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Filtered.Basic

import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Closed subschemes of affine-transition limits

## Implementation details

The inverse system is built from the scheme-theoretic images of the closed subscheme in the
stages; this argument is written directly rather than following the proof of Tag 0A0P.

## References

* Stacks Project, Limits, Tag 0A0P (approximation argument), and Morphisms, Tag 01R8 (quasi-compact
  scheme-theoretic images)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A closed subscheme `X` of the limit `Y` of a cofiltered diagram of qcqs schemes with affine
transitions is the limit of a compatible system of closed subschemes of the stages, with
affine transitions. -/
theorem exists_closedImmersion_system_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u})
    [∀ {j k : J} (a : j ⟶ k), IsAffineHom (D.map a)]
    [∀ j : J, CompactSpace (D.obj j)]
    [∀ j : J, QuasiSeparatedSpace (D.obj j)]
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (πY : (Functor.const J).obj Y ⟶ D) (hY : IsLimit (Cone.mk Y πY)) :
    ∃ (Z : J ⥤ Scheme.{u}) (k : Z ⟶ D)
      (πX : (Functor.const J).obj X ⟶ Z),
      Nonempty (IsLimit (Cone.mk X πX)) ∧
      (∀ {j k : J} (a : j ⟶ k), IsAffineHom (Z.map a)) ∧
      (∀ j : J, IsClosedImmersion (k.app j)) ∧
      (∀ j : J, πX.app j ≫ k.app j = i ≫ πY.app j) := by
  classical
  -- Reconstruct the ideal on the affine opens pulled back from one fixed stage.
  have hleft : i.ker ≤ ⨆ j : J, (i ≫ πY.app j).ker.comap (πY.app j) := by
    have hπ (j : J) : IsAffineHom (πY.app j) := isAffineHom_π_app D _ hY j
    let K : Y.IdealSheafData := ⨆ j : J, (i ≫ πY.app j).ker.comap (πY.app j)
    let j₀ : J := IsCofiltered.nonempty.some
    refine Scheme.IdealSheafData.le_of_iSup_eq_top
      (fun U : (D.obj j₀).affineOpens ↦ ⟨πY.app j₀ ⁻¹ᵁ U, U.2.preimage _⟩)
      ((πY.app j₀).iSup_preimage_eq_top (iSup_affineOpens_eq_top _)) ?_
    intro U s hs
    let W : Y.affineOpens := ⟨πY.app j₀ ⁻¹ᵁ U, U.2.preimage _⟩
    have hE (j : Over j₀) : IsAffine ((opensDiagram D j₀ U).obj j) :=
      U.2.preimage (D.map _)
    obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _
      (isLimitOpensCone D (Cone.mk Y πY) hY j₀ U) (W.1.topIso.inv s)
    let V : (D.obj j.left).affineOpens :=
      ⟨(D.map j.hom ⁻¹ᵁ U).ι ''ᵁ ⊤, by
        change IsAffineOpen _
        simpa only [Scheme.Opens.ι_image_top] using U.2.preimage (D.map j.hom)⟩
    change Γ(D.obj j.left, V.1) at t
    have hWV : W.1 ≤ πY.app j.left ⁻¹ᵁ V := by
      simp [W, V, ← Scheme.Hom.comp_preimage, (Cone.mk Y πY).w]
    have hVW : πY.app j.left ⁻¹ᵁ V ≤ W.1 := by
      simp [W, V, ← Scheme.Hom.comp_preimage, (Cone.mk Y πY).w]
    have ht' : (πY.app j.left).appLE V W.1 hWV t = s := by
      have ht₁ := congr(W.1.topIso.hom $ht)
      convert! ht₁ using 1
      · dsimp [V, Scheme.Opens.toScheme_presheaf_obj]
        rw [← ConcreteCategory.comp_apply]
        simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
      · simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id,
          ConcreteCategory.id_apply]
    have htker : t ∈ (i ≫ πY.app j.left).ker.ideal V := by
      rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
      have hz : i.app W.1 s = 0 := i.ideal_ker_le W hs
      have heq : (i ≫ πY.app j.left).appLE V (i ⁻¹ᵁ W.1) (by
          exact (i.preimage_mono hWV).trans (by rfl)) t = 0 := by
        rw [← Scheme.Hom.appLE_comp_appLE i (πY.app j.left) V W.1
          (i ⁻¹ᵁ W.1) hWV le_rfl, ConcreteCategory.comp_apply]
        convert! (congrArg (fun v ↦ i.app W.1 v) ht').trans hz using 1
        simp only [Scheme.Hom.app_eq_appLE]
        congr 1
      have he : (i ≫ πY.app j.left) ⁻¹ᵁ V = i ⁻¹ᵁ W.1 := by
        rw [Scheme.Hom.comp_preimage]
        exact congrArg (fun T ↦ i ⁻¹ᵁ T) (le_antisymm hVW hWV)
      let e : i ⁻¹ᵁ W.1 ≤ (i ≫ πY.app j.left) ⁻¹ᵁ V :=
        (i.preimage_mono hWV).trans (by rfl)
      have hres : IsIso (X.presheaf.map (homOfLE e).op) := by
        change IsIso (X.presheaf.map (eqToHom he.symm).op)
        infer_instance
      apply (ConcreteCategory.bijective_of_isIso
        (X.presheaf.map (homOfLE e).op)).1
      change (X.presheaf.map (homOfLE e).op).hom ((i ≫ πY.app j.left).app V t) =
        (X.presheaf.map (homOfLE e).op).hom 0
      simpa only [Scheme.Hom.appLE, CommRingCat.comp_apply, map_zero] using heq
    have hb : (i ≫ πY.app j.left).ker ≤ K.map (πY.app j.left) :=
      Scheme.IdealSheafData.le_map_iff_comap_le.mpr
        (le_iSup (fun l : J ↦ (i ≫ πY.app l).ker.comap (πY.app l)) j.left)
    have hb' := hb V htker
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at hb'
    have hb'' := K.ideal_le_comap_ideal (U := W)
      (V := ⟨πY.app j.left ⁻¹ᵁ V, V.2.preimage _⟩) hWV hb'
    change s ∈ K.ideal W
    rw [← ht']
    exact hb''
  let I : ∀ j : J, (D.obj j).IdealSheafData := fun j ↦ (i ≫ πY.app j).ker
  have hI {j l : J} (a : j ⟶ l) : I l ≤ (I j).map (D.map a) := by
    dsimp [I]
    rw [Scheme.IdealSheafData.map_ker, Category.assoc, (Cone.mk Y πY).w]
  let Z : J ⥤ Scheme.{u} :=
    { obj j := (I j).subscheme
      map a := Scheme.IdealSheafData.subschemeMap _ _ (D.map a) (hI a)
      map_id j := by simp [← cancel_mono (I j).subschemeι]
      map_comp a b := by simp [← cancel_mono (I _).subschemeι] }
  let k : Z ⟶ D :=
    { app j := (I j).subschemeι
      naturality j l a := by simp [Z] }
  let πX : (Functor.const J).obj X ⟶ Z :=
    { app j := (i ≫ πY.app j).toImage
      naturality j l a := by
        dsimp [Z, I]
        rw [← cancel_mono (i ≫ πY.app l).imageι]
        simp [Category.assoc, (Cone.mk Y πY).w] }
  have hfac (j : J) : πX.app j ≫ k.app j = i ≫ πY.app j := by
    exact (i ≫ πY.app j).toImage_imageι
  have hker : i.ker = ⨆ j : J, (I j).comap (πY.app j) := by
    apply le_antisymm hleft
    refine iSup_le fun j ↦ ?_
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.map_ker]
  have hlimit : IsLimit (Cone.mk X πX) :=
    { lift s := IsClosedImmersion.lift i
        (hY.lift ((Cone.postcompose k).obj s)) (by
          rw [hker]
          refine iSup_le fun j ↦ ?_
          rw [← Scheme.IdealSheafData.le_map_iff_comap_le,
            ← Scheme.Hom.ker_comp, hY.fac]
          rw [← Scheme.IdealSheafData.ker_subschemeι (I j)]
          exact Scheme.Hom.le_ker_comp (s.π.app j) (k.app j))
      fac s j := by
        rw [← cancel_mono (k.app j), Category.assoc, hfac]
        simp [← Category.assoc, hY.fac]
      uniq s m hm := by
        rw [← cancel_mono i]
        simp only [IsClosedImmersion.lift_fac]
        apply hY.hom_ext
        intro j
        rw [Category.assoc, ← hfac, ← Category.assoc, hm]
        exact (hY.fac ((Cone.postcompose k).obj s) j).symm }
  refine ⟨Z, k, πX, ⟨hlimit⟩, ?_, ?_, hfac⟩
  · intro j l a
    have : IsAffineHom (Z.map a ≫ k.app l) := by
      change IsAffineHom
        (Scheme.IdealSheafData.subschemeMap _ _ (D.map a) (hI a) ≫ (I l).subschemeι)
      rw [Scheme.IdealSheafData.subschemeMap_subschemeι]
      infer_instance
    exact IsAffineHom.of_comp (Z.map a) (k.app l)
  · intro j
    change IsClosedImmersion (I j).subschemeι
    infer_instance

end AlgebraicGeometry
