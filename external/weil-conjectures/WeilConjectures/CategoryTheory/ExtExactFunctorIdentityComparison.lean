/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Ext identity comparison

Source: Stacks Project, derived.tex, Tag 015F; Mathlib Ext.Map.

The comparison is obtained directly from Mathlib's
`LocalizerMorphism.equiv_smallShiftedHomMap`, specializing the localized functor to
the identity. No injective resolutions or separate Ext composition comparison are needed.
(blueprint: lem-weil-pbc-ext-exact-functor-identity-comparison)
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

-- Retained for HigherDirectImageRawPullbackIdentity, which imports this module with `all`.

/-- Shift compatibility descends along localization: check the square after precomposition,
then cancel the image of the localization functor's shift comparison. -/
private theorem commShift_of_localization
    {A B : Type*} [Category A] [Category B]
    {W : MorphismProperty A} (L : A ⥤ B) [L.IsLocalization W]
    [HasShift A ℤ] [HasShift B ℤ] [L.CommShift ℤ]
    {F G : B ⥤ B} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift (Functor.whiskerLeft L τ) ℤ] :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  apply Localization.natTrans_ext L W
  intro K
  dsimp
  rw [← cancel_epi (F.map ((L.commShiftIso n).hom.app K))]
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft L τ) n K
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc, ← τ.naturality_assoc] using h

/-- An exact functor isomorphic to the identity acts on Ext by that comparison.
Source: Stacks Project, derived.tex, Tag 015F, and Mathlib Ext.Map.

Proof: represent x by a shifted morphism between single complexes in the derived
category. The identity functor on complexes induces the identity after localization.
The components of e induce the corresponding isomorphism from the functor induced by F
to the identity. Naturality for the shifted morphism is exactly the displayed square.
After cancelling the canonical comparisons with single complexes and shifts, its
components are Ext.mk₀ (e.hom.app X) and Ext.mk₀ (e.hom.app Y).
(blueprint: lem-weil-pbc-ext-exact-functor-identity-comparison)
-/
theorem exactFunctorIdentityComparison
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp x (zero_add n) := by
  -- The pinned Ext.Map has no mapExactFunctor_eq_of_iso or mapExactFunctor_id API.
  -- Use its localization comparison directly, without an EnoughInjectives hypothesis.
  let := HasDerivedCategory.standard C
  let Q := DerivedCategory.Q (C := C)
  let η := NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)
  -- Check the composite termwise comparison before whiskering by the localization.
  have : NatTrans.CommShift η.hom ℤ := by
    constructor
    intro m
    ext K i
    dsimp [η]
    simp [Functor.commShiftIso_id_hom_app]
  let δ := Functor.isoWhiskerRight η Q ≪≫ Q.leftUnitor ≪≫ Q.rightUnitor.symm
  have : NatTrans.CommShift Q.rightUnitor.inv ℤ :=
    NatTrans.CommShift.of_iso_inv Q.rightUnitor ℤ
  have : NatTrans.CommShift δ.hom ℤ := by dsimp [δ]; infer_instance
  have hmap := (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).equiv_smallShiftedHomMap Q Q
      ((F.mapCochainComplexSingleFunctor 0).app X)
      ((F.mapCochainComplexSingleFunctor 0).app Y) (𝟭 _) δ x
  have hx (Z : C) :
      Q.map ((F.mapCochainComplexSingleFunctor 0).app Z).inv ≫
        δ.hom.app ((CochainComplex.singleFunctor C 0).obj Z) =
      (DerivedCategory.singleFunctor C 0).map (e.hom.app Z) := by
    dsimp [δ]
    simp only [Category.comp_id, ← Q.map_comp]
    change Q.map _ = Q.map _
    congr 1
    apply HomologicalComplex.from_single_hom_ext
    dsimp [Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex, η,
      NatIso.mapHomologicalComplex, Functor.mapHomologicalComplexIdIso,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single]
    simp
  have hy (Z : C) :
      δ.inv.app ((CochainComplex.singleFunctor C 0).obj Z) ≫
        Q.map ((F.mapCochainComplexSingleFunctor 0).app Z).hom ≫
          (DerivedCategory.singleFunctor C 0).map (e.hom.app Z) = 𝟙 _ := by
    rw [← hx Z]
    dsimp only [Iso.app_hom, Iso.app_inv]
    rw [← Q.map_comp_assoc, Iso.hom_inv_id_app]
    erw [Q.map_id, Category.id_comp, Iso.inv_hom_id_app]
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  change (x.mapExactFunctor F).hom = _ at hmap
  rw [hmap]
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.id_map,
    Category.assoc, ← Functor.map_comp, hy, hx]
  change _ ≫ x.hom ≫ (shiftFunctor _ _).map (𝟙 _) = _
  simp

end CategoryTheory.Abelian.Ext
