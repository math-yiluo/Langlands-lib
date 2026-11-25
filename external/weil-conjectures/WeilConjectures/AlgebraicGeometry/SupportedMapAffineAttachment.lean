/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.SupportedMapAffineUnionGluing
import WeilConjectures.AlgebraicGeometry.SupportedMapInitialAmbientLift
import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationData

/-! # One affine attachment for supported stabilized maps

Source: Stacks Project, Tag 09IM.
(blueprint: lem-sc-supported-map-affine-attachment).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem restrict_map_comparison
    {C D B : Type*} [Category C] [Category D] [Category B]
    (L : C ⥤ D) (H : D ⥤ B) (J : C ⥤ B) (c : L ⋙ H ≅ J)
    {R E : C} {F : D} {S : B} (β : R ⟶ E) (α : F ⟶ L.obj E)
    (d : L.obj R ≅ F) (e : H.obj F ≅ S) (a : S ⟶ J.obj E)
    (hd : L.map β = d.hom ≫ α) (he : H.map α ≫ c.hom.app E = e.hom ≫ a) :
    J.map β = (c.symm.app R ≪≫ H.mapIso d ≪≫ e).hom ≫ a := by
  have hn := c.hom.naturality β
  calc
    J.map β = c.inv.app R ≫ H.map (L.map β) ≫ c.hom.app E := by
      simpa only [Functor.comp_map, Category.assoc, Iso.inv_hom_id_app_assoc] using
        (congrArg (fun f ↦ c.inv.app R ≫ f) hn).symm
    _ = c.inv.app R ≫ H.map d.hom ≫ e.hom ≫ a := by
      rw [hd, H.map_comp]
      simp only [Category.assoc]
      rw [he]
    _ = _ := by
      simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
        Functor.mapIso_hom, Category.assoc]

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Attaching a single affine open extends the source plus its shift.
The input source need only be perfect and supported on the old open; its behaviour
elsewhere in X is immaterial.
Source: Stacks Project, Tag 09IM, the case X = U union V in its proof.
(blueprint: lem-sc-supported-map-affine-attachment).

Proof: Restrict R and β to W. Its pointwise local perfect models make this
restriction perfect, and its cohomology stalks vanish on W minus T. On W replace
R by R plus R[1] and β by the first projection followed by β. The intersection
W intersect V is quasi-compact by quasi-separatedness, as is V minus T.
On the affine V apply supported perfect extension to R restricted to the
intersection. This yields Q supported on T intersect V and an identification with
(R plus R[1]) on the intersection. Compose the identification with the projection
and restricted β. Affine perfect map lifting replaces Q by a perfect tensor
augmentation, unchanged on the intersection and still supported on T intersect V,
and lifts the composite to E restricted to V. Derived open gluing gives a source
and map on W union V. At points of W or V its local models are strictly perfect,
and its stalks vanish away from T. Extend this source and map by zero from W union V
to X, using the exact derived adjunction. This does not affect those local properties.
On U restrict the gluing identification and apply the biproduct and shift
restriction comparisons. The resulting isomorphism identifies the restricted
map with the first projection followed by β restricted to U.
All comparisons are induced by Modules.overEquiv and iterated overFunctorMap.
No support or perfectness outside W union V is required. Empty or redundant V
still works, and the zero source uses the same construction. -/
theorem exists_supported_map_affine_attachment
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (U W V : X.Opens) (hUW : U ≤ W) (hW : IsCompact (W : Set X))
    (hV : IsAffineOpen V) (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedQCohCategory X)
    (R : schemeDerivedCategory X) (β : R ⟶ E.obj)
    (hR : (∀ x : X, x ∈ W → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
              DerivedCategory.Q.obj K)))
    (hRT : (∀ (i : ℤ) (x : X), x ∈ W → x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x))))
    :
    ∃ (R' : schemeDerivedCategory X) (β' : R' ⟶ E.obj),
      (∀ x : X, x ∈ (W ⊔ V) → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R' ≅
              DerivedCategory.Q.obj K)) ∧
      (∀ (i : ℤ) (x : X), x ∈ (W ⊔ V) → x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R').val.presheaf x))) ∧
      ∃ e : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R' ≅
          ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R ⊞
            (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R)⟦(1 : ℤ)⟧,
        ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β' =
          e.hom ≫ biprod.fst ≫ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β := by
  classical
  -- Cache the sheaf-category structures used by the restriction and lifting steps.
  let : ∀ Z : Scheme.{u}, Abelian (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) :=
    fun Z ↦ inferInstance
  let : ∀ (Z : Scheme.{u}) (O : Z.Opens),
      Abelian (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over O)) :=
    fun Z O ↦ inferInstance
  let Y := W ⊔ V
  -- Destructure a named hypothesis to avoid generalizing an application across the large goal.
  have hlocalY := open_derived_localization_data X Y
  obtain ⟨hY, ⟨hYO⟩⟩ := hlocalY
  let := hY
  let := hYO
  let L := schemeOpenRestriction X Y
  let H := schemeOpenOverlapRestriction X
    (homOfLE (le_trans hUW le_sup_left) : U ⟶ Y)
  let J := schemeOpenRestriction X U
  let c : L.mapDerivedCategory ⋙ H.mapDerivedCategory ≅ J.mapDerivedCategory :=
    schemeDerivedOpenRestrictionCompIso X (homOfLE (le_trans hUW le_sup_left) : U ⟶ Y)
  have hunion :=
    exists_supported_map_affine_union_gluing X U W V hUW hW hV T hT hTc E R β hR hRT c
  obtain ⟨F, α, hF, hFT, e, he⟩ := hunion
  have hambient :=
    exists_supported_map_initial_ambient_lift X Y T E F hF hFT α
  obtain ⟨R', β', hR', hRT', d, hd⟩ := hambient
  refine ⟨R', β', hR', hRT', c.symm.app R' ≪≫ H.mapDerivedCategory.mapIso d ≪≫ e, ?_⟩
  change J.mapDerivedCategory.map β' =
    (c.symm.app R' ≪≫ H.mapDerivedCategory.mapIso d ≪≫ e).hom ≫
      biprod.fst ≫ J.mapDerivedCategory.map β
  exact restrict_map_comparison L.mapDerivedCategory H.mapDerivedCategory
    J.mapDerivedCategory c β' α d e (biprod.fst ≫ J.mapDerivedCategory.map β) hd he

end AlgebraicGeometry.Scheme
