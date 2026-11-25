/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeOpenUnit
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeNaturality
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionUnitIso

/-! # Open component compatibility for derived base change

Source: Stacks Project, Tags 08HY, 08BV and 0DJ9.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restriction_unit_generic
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {M : C ⥤ E} {S : E ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (H : D ⥤ E) (t : L ⋙ H ≅ M) (K : C) :
    a.unit.app K ≫ b.homEquiv _ _
        (t.inv.app (R.obj (L.obj K)) ≫ H.map (a.counit.app (L.obj K)) ≫
          t.hom.app K) = b.unit.app K := by
  rw [← b.homEquiv_naturality_left]
  have hn := t.inv.naturality (a.unit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  have ht : M.map (a.unit.app K) ≫
      (t.inv.app (R.obj (L.obj K)) ≫ H.map (a.counit.app (L.obj K)) ≫
        t.hom.app K) = 𝟙 _ := by
    rw [← Category.assoc, hn]
    simp only [Category.assoc, ← H.map_comp_assoc, a.left_triangle_components,
      H.map_id, Category.id_comp, Iso.inv_hom_id_app, Functor.id_obj]
  rw [ht]
  simpa only [Functor.id_obj] using b.homEquiv_id K

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem precomp_rightAdjoint_injective
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {A B : C} (u : A ⟶ B) [IsIso (L.map u)] {T : D}
    {f g : B ⟶ R.obj T} (h : u ≫ f = u ≫ g) : f = g := by
  apply (a.homEquiv B T).symm.injective
  apply (cancel_epi (L.map u)).mp
  simpa only [a.homEquiv_naturality_left_symm] using
    congrArg (a.homEquiv A T).symm h

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

private theorem open_restriction_unit
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) (K : schemeDerivedCategory X) :
    (mvOpenRestrictionAdjunction X U).unit.app K ≫
        schemeDerivedOpenDirectImageRestriction X i
          (mvOpenRestrictionAdjunction X U) (mvOpenRestrictionAdjunction X W) K =
      (mvOpenRestrictionAdjunction X W).unit.app K := by
  exact restriction_unit_generic (mvOpenRestrictionAdjunction X U)
    (mvOpenRestrictionAdjunction X W) (schemeOpenOverlapRestriction X i).mapDerivedCategory
    (schemeDerivedOpenRestrictionCompIso X i) K

private theorem nested_open_unit_isIso
    {X X' : Scheme.{u}} (q : X' ⟶ X) {W U : X.Opens} (i : W ⟶ U)
    (K : schemeDerivedCategory X) :
    IsIso ((schemeOpenRestriction X' (q ⁻¹ᵁ W)).mapDerivedCategory.map
      ((derivedPullback q).map ((mvOpenRestrictionAdjunction X U).unit.app K))) := by
  let u := (mvOpenRestrictionAdjunction X U).unit.app K
  have : IsIso ((schemeOpenRestriction X U).mapDerivedCategory.map u) :=
    schemeDerivedOpen_unit_isIso X U (mvOpenRestrictionAdjunction X U) K
  have : IsIso (((schemeOpenRestriction X U).mapDerivedCategory ⋙
      (schemeOpenOverlapRestriction X i).mapDerivedCategory).map u) := by
    change IsIso ((schemeOpenOverlapRestriction X i).mapDerivedCategory.map
      ((schemeOpenRestriction X U).mapDerivedCategory.map u))
    infer_instance
  have : IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map u) :=
    (NatIso.isIso_map_iff (schemeDerivedOpenRestrictionCompIso X i) u).mp inferInstance
  have : IsIso (((schemeOpenRestriction X W).mapDerivedCategory ⋙
      derivedPullback (q.resLE W (q ⁻¹ᵁ W) le_rfl)).map u) := by
    change IsIso ((derivedPullback (q.resLE W (q ⁻¹ᵁ W) le_rfl)).map
      ((schemeOpenRestriction X W).mapDerivedCategory.map u))
    infer_instance
  exact (NatIso.isIso_map_iff (mvPullbackOpenRestrictionIso q W) u).mpr inferInstance

private theorem open_restriction_square
    {X X' : Scheme.{u}} (q : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback q).obj K ⟶ K') {W U : X.Opens} (i : W ⟶ U) :
    let aU := schemeDerivedBaseChangeMap U.ι (q ⁻¹ᵁ U).ι q
      (q.resLE U (q ⁻¹ᵁ U) le_rfl) (Scheme.Hom.resLE_comp_ι q le_rfl)
      ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ≫
        (schemeDerivedDirectImage (q ⁻¹ᵁ U).ι).map
          ((mvPullbackOpenRestrictionIso q U).inv.app K ≫
            (schemeOpenRestriction X' (q ⁻¹ᵁ U)).mapDerivedCategory.map ψ)
    let aW := schemeDerivedBaseChangeMap W.ι (q ⁻¹ᵁ W).ι q
      (q.resLE W (q ⁻¹ᵁ W) le_rfl) (Scheme.Hom.resLE_comp_ι q le_rfl)
      ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ≫
        (schemeDerivedDirectImage (q ⁻¹ᵁ W).ι).map
          ((mvPullbackOpenRestrictionIso q W).inv.app K ≫
            (schemeOpenRestriction X' (q ⁻¹ᵁ W)).mapDerivedCategory.map ψ)
    (derivedPullback q).map (schemeDerivedOpenDirectImageRestriction X i
        (mvOpenRestrictionAdjunction X U) (mvOpenRestrictionAdjunction X W) K) ≫ aW =
      aU ≫ schemeDerivedOpenDirectImageRestriction X' ((Opens.map q.base).map i)
        (mvOpenRestrictionAdjunction X' (q ⁻¹ᵁ U))
        (mvOpenRestrictionAdjunction X' (q ⁻¹ᵁ W)) K' := by
  intro aU aW
  let u := (mvOpenRestrictionAdjunction X U).unit.app K
  have := nested_open_unit_isIso q i K
  apply precomp_rightAdjoint_injective (mvOpenRestrictionAdjunction X' (q ⁻¹ᵁ W))
    ((derivedPullback q).map u)
  calc
    _ = (derivedPullback q).map
          ((mvOpenRestrictionAdjunction X W).unit.app K) ≫ aW := by
      rw [← Category.assoc, ← Functor.map_comp, open_restriction_unit]
    _ = ψ ≫ (mvOpenRestrictionAdjunction X' (q ⁻¹ᵁ W)).unit.app K' :=
      mvOpenBaseChange_unit q K K' ψ W
    _ = _ := by
      rw [← Category.assoc, mvOpenBaseChange_unit q K K' ψ U,
        Category.assoc, open_restriction_unit]

/-- Base-change components commute with restriction to a nested open.
Source: Stacks Project, Cohomology, Lemma 08BV and Remark 08HY;
Perfect Complexes, Tag 0DJ9, induction step, using Tag 0D5S.
(blueprint: lem-pc-rf-mv-open-base-change-restriction).
Proof: The transpose defining nested-open restriction sends the unit of the
larger open to the unit of the smaller open, by the left triangle identity.
Restriction of an open-adjunction unit to that open is invertible. Restrict
further to the smaller open and transport across the pullback/restriction
comparison; the pulled-back larger-open unit is still inverted by restriction
to the smaller open. The smaller-open adjunction therefore makes precomposition
with that unit injective on maps into its right adjoint. After precomposition,
the desired local square follows from the two open base-change unit identities
and the nested-open unit identity. Finally, naturality of base change in the
coefficient object and functoriality of Rf'_* give the displayed square.
No cover or finiteness assumption enters this argument. Equal and empty opens
are included, since the adjunction identities and invertibility remain valid. -/
theorem mvBaseChangeOpenMap_restriction
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback g').obj K ⟶ K')
    {W U : X.Opens} (i : W ⟶ U) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map
        (schemeDerivedOpenDirectImageRestriction X i
          (mvOpenRestrictionAdjunction X U) (mvOpenRestrictionAdjunction X W) K) ≫
      mvBaseChangeOpenMap f f' g g' h K K' ψ W =
    mvBaseChangeOpenMap f f' g g' h K K' ψ U ≫
      (schemeDerivedDirectImage f').map
        (schemeDerivedOpenDirectImageRestriction X' ((Opens.map g'.base).map i)
          (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
          (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)) K')  := by
  dsimp only [mvBaseChangeOpenMap]
  have hn := schemeDerivedBaseChangeMap_naturality f f' g g' h
    (schemeDerivedOpenDirectImageRestriction X i
      (mvOpenRestrictionAdjunction X U) (mvOpenRestrictionAdjunction X W) K)
  dsimp only [Functor.id_obj, Functor.comp_obj] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [open_restriction_square g' K K' ψ i]
  simp only [Category.assoc]


end AlgebraicGeometry
