/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.SupportedAffineOverlapMap
public import WeilConjectures.AlgebraicGeometry.SupportedRelativeOpenGluing
public import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationData

/-! # Supported perfect gluing on the union with an affine open

Source: Stacks Project, Tag 09IM, two-open construction before ambient extension.
(blueprint: lem-sc-supported-map-affine-union-gluing).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def relative_restriction_comp_iso
    (X : Scheme.{u}) (U W Y : X.Opens) (hUW : U ≤ W) (hWY : W ≤ Y) :
    schemeOpenOverlapRestriction X (homOfLE hWY) ⋙
      schemeOpenOverlapRestriction X (homOfLE hUW) ≅
    schemeOpenOverlapRestriction X (homOfLE (le_trans hUW hWY)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Modules.overEquiv Y).inverse
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWY))
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (Modules.overEquiv W).unitIso.symm _ ≪≫
              Functor.leftUnitor _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Iso.refl (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE (le_trans hUW hWY))))
          (Modules.overEquiv U).functor)

private theorem stabilized_map_restriction
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    [Preadditive A] [Preadditive B] [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    [HasShift A ℤ] [HasShift B ℤ]
    (L : C ⥤ D) (H : D ⥤ B) (J : C ⥤ B) (JW : C ⥤ A)
    (P : D ⥤ A) (Q : A ⥤ B) [Q.Additive] [Q.CommShift ℤ]
    (d : H ≅ P ⋙ Q) (kW : L ⋙ P ≅ JW) (kU : JW ⋙ Q ≅ J) (c : L ⋙ H ≅ J)
    (E R : C) (β : R ⟶ E) (F : D) (α : F ⟶ L.obj E)
    (iW : P.obj F ≅ JW.obj R ⊞ (JW.obj R)⟦(1 : ℤ)⟧)
    (hα : P.map α ≫ kW.hom.app E = iW.hom ≫ biprod.fst ≫ JW.map β) :
    ∃ e : H.obj F ≅ J.obj R ⊞ (J.obj R)⟦(1 : ℤ)⟧,
      H.map α ≫ c.hom.app E = e.hom ≫ biprod.fst ≫ J.map β := by
  have : PreservesBinaryBiproducts Q := preservesBinaryBiproducts_of_preservesBiproducts Q
  let k : L ⋙ H ≅ J :=
    Functor.isoWhiskerLeft L d ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight kW Q ≪≫ kU
  let e₀ : H.obj F ≅ J.obj R ⊞ (J.obj R)⟦(1 : ℤ)⟧ :=
    d.app F ≪≫ Q.mapIso iW ≪≫ Q.mapBiprod (JW.obj R) ((JW.obj R)⟦(1 : ℤ)⟧) ≪≫
      biprod.mapIso (kU.app R)
        ((Q.commShiftIso (1 : ℤ)).app (JW.obj R) ≪≫
          (shiftFunctor _ (1 : ℤ)).mapIso (kU.app R))
  have he₀ : H.map α ≫ k.hom.app E = e₀.hom ≫ biprod.fst ≫ J.map β := by
    have hk : k.hom.app E = d.hom.app (L.obj E) ≫ Q.map (kW.hom.app E) ≫
        kU.hom.app E := by simp [k]
    rw [hk, ← Category.assoc, ← Category.assoc, d.hom.naturality α]
    simp only [Functor.comp_map, Category.assoc]
    rw [← Q.map_comp_assoc, hα, Q.map_comp]
    simp only [e₀, Iso.trans_hom, Functor.mapIso_hom, Functor.mapBiprod_hom,
      biprod.mapIso_hom, Category.assoc, biprod.map_fst_assoc, biprod.lift_fst_assoc]
    simp only [Q.map_comp, Category.assoc]
    have hu := kU.hom.naturality β
    simp only [Functor.comp_map] at hu
    rw [hu]
    rfl
  let t : J ≅ J := k.symm ≪≫ c
  let e : H.obj F ≅ J.obj R ⊞ (J.obj R)⟦(1 : ℤ)⟧ :=
    e₀ ≪≫ biprod.mapIso (t.app R) ((shiftFunctor _ (1 : ℤ)).mapIso (t.app R))
  refine ⟨e, ?_⟩
  calc
    H.map α ≫ c.hom.app E = (H.map α ≫ k.hom.app E) ≫ t.hom.app E := by simp [t]
    _ = (e₀.hom ≫ biprod.fst ≫ J.map β) ≫ t.hom.app E := by rw [he₀]
    _ = e₀.hom ≫ biprod.fst ≫ t.hom.app R ≫ J.map β := by
      rw [Category.assoc, Category.assoc, ← t.hom.naturality β]
    _ = e.hom ≫ biprod.fst ≫ J.map β := by
      simp only [e, Iso.trans_hom, biprod.mapIso_hom, Category.assoc,
        biprod.map_fst_assoc, Iso.app_hom]

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- The affine construction produces a perfect supported source on the union itself.
There is no ambient extension in this statement. The supplied natural comparison `c`
identifies iterated restriction through the union with direct restriction to `U`.
Source: Stacks Project, Tag 09IM, proof assuming a two-open cover, using Tags 08EK,
08EH, and 08DG.
(blueprint: lem-sc-supported-map-affine-union-gluing).

Proof: Restrict the source R to W. Intersect each strictly perfect neighbourhood
with W and transport its bounded finite-free retract model through Modules.overEquiv;
this proves perfectness on W. Exact restriction identifies the cohomology stalks,
so the source is supported on T intersect W. Restrict E to the union and its two
opens; exact restriction preserves quasi-coherent cohomology. Quasi-separatedness
makes W intersect V compact, since both W and V are compact opens. It also makes
V intersect the open complement of T compact. Thus the affine supported extension
lemma on V extends the source on W intersect V after adjoining its shift. Compose
its overlap identification with the first projection and the restricted beta.
Affine perfect map lifting supplies a tensor augmentation, invertible on the
overlap, with a lifted map to E restricted to V. Its perfect source remains
supported on T intersect V. Derived open gluing on Y = W union V combines this
map with the first-projection map on W. The resulting F is perfect at every point
of Y and its cohomology stalks vanish outside T, by the two local identifications.
Restrict the W identification to U; the biproduct and shift comparisons identify
it with R restricted to U plus its shift. For the canonical comparison k this gives
an isomorphism e0 and the required map identity with k. For an arbitrary c, let t = k.symm
followed by c, a natural
automorphism of direct restriction J. Postcompose e0 with the biproduct of t at R
and the shift of that same isomorphism. The first projection of this biproduct
is the old first projection followed by t at R. Naturality of t at beta then
changes the equation with k into the equation with c. This does not require c
to commute with shifts. No extension from Y to X occurs here.
If U, W, V or T is empty, the same construction applies with the zero restrictions;
if V is already contained in W the stabilized source on W supplies the gluing. -/
theorem exists_supported_map_affine_union_gluing
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
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    [∀ O : (W ⊔ V).toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (W ⊔ V).toScheme.toRingedSpace).over O))]
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
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x)))) :
    let Y := W ⊔ V
    let L := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Y ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Y))
        (D := SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace))
        (Modules.overEquiv Y)
    let H := Equivalence.inverse
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Y))
        (D := SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace))
        (Modules.overEquiv Y) ⋙
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (le_trans hUW le_sup_left)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    let J := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    ∀ c : L.mapDerivedCategory ⋙ H.mapDerivedCategory ≅ J.mapDerivedCategory,
    ∃ (F : schemeDerivedCategory Y.toScheme) (α : F ⟶ L.mapDerivedCategory.obj E.obj),
      IsPerfect Y.toScheme F ∧
      (∀ (i : ℤ) (x : Y.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace)) i).obj F).val.presheaf x))) ∧
      ∃ e : H.mapDerivedCategory.obj F ≅
          J.mapDerivedCategory.obj R ⊞ (J.mapDerivedCategory.obj R)⟦(1 : ℤ)⟧,
        H.mapDerivedCategory.map α ≫ c.hom.app E.obj =
          e.hom ≫ biprod.fst ≫ J.mapDerivedCategory.map β := by
  classical
  -- Cache the sheaf-category structures used by the restriction and lifting steps.
  let : ∀ Z : Scheme.{u}, Abelian (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) :=
    fun Z ↦ inferInstance
  let : ∀ (Z : Scheme.{u}) (O : Z.Opens),
      Abelian (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over O)) :=
    fun Z O ↦ inferInstance
  let Y := W ⊔ V
  let L := (schemeOpenRestriction X Y).mapDerivedCategory
  let H := (schemeOpenOverlapRestriction X
    (homOfLE (le_trans hUW le_sup_left) : U ⟶ Y)).mapDerivedCategory
  let J := (schemeOpenRestriction X U).mapDerivedCategory
  change ∀ c : L ⋙ H ≅ J,
    ∃ (F : schemeDerivedCategory Y.toScheme) (α : F ⟶ L.obj E.obj),
      IsPerfect Y.toScheme F ∧
      (∀ (i : ℤ) (x : Y.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace)) i).obj F).val.presheaf
            x))) ∧
      ∃ e : H.obj F ≅ J.obj R ⊞ (J.obj R)⟦(1 : ℤ)⟧,
        H.map α ≫ c.hom.app E.obj = e.hom ≫ biprod.fst ≫ J.map β
  intro c
  -- Destructure a named hypothesis to avoid generalizing an application across the large goal.
  have hlocalW := open_derived_localization_data X W
  obtain ⟨hDW, ⟨hOW⟩⟩ := hlocalW
  let := hDW
  let := hOW
  have hlocalV := open_derived_localization_data X V
  obtain ⟨hDV, ⟨hOV⟩⟩ := hlocalV
  let := hDV
  let := hOV
  have hlocalI := open_derived_localization_data X (W ⊓ V)
  obtain ⟨hDI, ⟨hOI⟩⟩ := hlocalI
  let := hDI
  let := hOI
  let JW := (schemeOpenRestriction X W).mapDerivedCategory
  let P := (schemeOpenOverlapRestriction X
    (homOfLE le_sup_left : W ⟶ Y)).mapDerivedCategory
  let Q := (schemeOpenOverlapRestriction X (homOfLE hUW : U ⟶ W)).mapDerivedCategory
  let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ Y)
  let kU := schemeDerivedOpenRestrictionCompIso X (homOfLE hUW : U ⟶ W)
  let A := JW.obj R ⊞ (JW.obj R)⟦(1 : ℤ)⟧
  have hoverlap :=
    exists_supported_affine_overlap_map X W V hW hV T hT hTc E R β hR hRT
  obtain ⟨hA, hAT, B, b, s, hB, hBT, hs⟩ := hoverlap
  have hgluing :=
    exists_supported_relative_open_gluing X W V T A B hA hB hAT hBT
      s E.obj (biprod.fst ≫ JW.map β) b hs
  obtain ⟨F, α, hF, hFT, iW, _iV, hα, _hαV⟩ := hgluing
  let d : H ≅ P ⋙ Q :=
    (Functor.mapDerivedCategoryNatIso
      (relative_restriction_comp_iso X U W Y hUW le_sup_left)).symm ≪≫
      (Functor.mapDerivedCategoryCompIso
        (schemeOpenOverlapRestriction X (homOfLE le_sup_left : W ⟶ Y))
        (schemeOpenOverlapRestriction X (homOfLE hUW : U ⟶ W))).symm
  have : Q.Additive := inferInstance
  have hstabilized := stabilized_map_restriction L H J JW P Q d kW kU c
    E.obj R β F α iW hα
  obtain ⟨e, he⟩ := hstabilized
  exact ⟨F, α, hF, hFT, e, he⟩

end AlgebraicGeometry.Scheme
