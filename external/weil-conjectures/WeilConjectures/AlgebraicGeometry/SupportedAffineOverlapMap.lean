/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift
import WeilConjectures.AlgebraicGeometry.SupportedOverlapPerfectExtension
import WeilConjectures.AlgebraicGeometry.LocalPerfectSupportedStabilization
import WeilConjectures.AlgebraicGeometry.CompactOverlapRestrictionModel
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh

/-! # Supported affine overlap data

Source: Stacks Project, Tag 09IM, the construction on the affine member before gluing.
(blueprint: lem-sc-supported-affine-overlap-map).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem map_lift_transport
    {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) (S : C ⥤ H) (e : D ≌ H) (d : L ⋙ e.functor ≅ S)
    {Q B E : C} (α : S.obj Q ⟶ S.obj E) (bU : L.obj B ≅ L.obj Q)
    (b : B ⟶ E)
    (h : e.functor.preimage (d.hom.app Q ≫ α ≫ d.inv.app E) = bU.inv ≫ L.map b) :
    α = ((d.app Q).inv ≫ e.functor.map bU.inv ≫ (d.app B).hom) ≫ S.map b := by
  have hh := congrArg e.functor.map h
  rw [Functor.map_preimage, Functor.map_comp] at hh
  have hn := d.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  calc
    α = d.inv.app Q ≫ (d.hom.app Q ≫ α ≫ d.inv.app E) ≫ d.hom.app E := by
      simp only [Category.assoc, d.inv_hom_id_app_assoc, d.inv_hom_id_app,
        Category.comp_id]
    _ = d.inv.app Q ≫ (e.functor.map bU.inv ≫ e.functor.map (L.map b)) ≫
        d.hom.app E := by rw [hh]
    _ = _ := by
      simp only [Category.assoc]
      rw [hn]
      rfl

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Construct the affine member and its compatible overlap map; no object on the union
is asserted. Source: Stacks Project, Tag 09IM, first two-open paragraph, Tags 08EK and 08EH.
(blueprint: lem-sc-supported-affine-overlap-map).

Proof: Restrict R to W and transport its strictly perfect neighbourhood models through
Modules.overEquiv, intersecting each neighbourhood with W. The stabilized restriction A
is perfect, since biproducts and shifts preserve bounded finite-free retract models.
Exact restriction and its stalk comparison show that A is supported on T intersect W.
The overlap W intersect V is compact by quasi-separatedness. On V the pullback of T is
closed, and its complement is compact: intersect the compact open V with the compact
open complement of T and transport through the open embedding. Apply the affine supported
extension theorem to R restricted to this overlap. Identify its restriction with A on the
overlap using the exact functors' biproduct and shift comparisons. Compose the inverse of
this identification with the restricted first-projection map a. Restriction of E to V
has quasi-coherent cohomology by the open restriction criterion. Apply affine perfect map
lifting to the overlap map: its augmented source B is perfect and supported on T intersect
V, and its augmentation is invertible on the overlap. Compose this inverse augmentation
with the previous identification to get c:A|overlap ≅ B|overlap. The lifting identity gives
the stated compatibility of a and b, with the canonical iterated restriction comparisons.
Empty W, V, the overlap, or T require no separate choices; the same zero restrictions and
supported affine extension and lifting theorems apply. -/
theorem exists_supported_affine_overlap_map
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W V : X.Opens) (hW : IsCompact (W : Set X)) (hV : IsAffineOpen V)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ O : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [∀ O : V.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
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
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let A := JW.obj R ⊞ (JW.obj R)⟦(1 : ℤ)⟧
    let a : A ⟶ JW.obj E.obj := biprod.fst ≫ JW.map β
    IsPerfect W.toScheme A ∧
      (∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj A).val.presheaf x))) ∧
      ∃ (B : schemeDerivedCategory V.toScheme) (b : B ⟶ JV.obj E.obj)
        (c : SW.obj A ≅ SV.obj B),
        IsPerfect V.toScheme B ∧
        (∀ (i : ℤ) (x : V.toScheme), x.val ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) i).obj B).val.presheaf
              x))) ∧
        SW.map a ≫ kW.hom.app E.obj = c.hom ≫ SV.map b ≫ kV.hom.app E.obj := by
  classical
  -- Cache the sheaf-category structures used by the restriction and lifting steps.
  let : ∀ Z : Scheme.{u}, Abelian (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) :=
    fun Z ↦ inferInstance
  let : ∀ (Z : Scheme.{u}) (O : Z.Opens),
      Abelian (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over O)) :=
    fun Z O ↦ inferInstance
  intro JW JV SW SV kW kV A a
  -- Destructure a named hypothesis to avoid generalizing an application across the large goal.
  have hstabilization := local_perfect_supported_stabilization X W T R hR hRT
  obtain ⟨hF, hFT, hA, hAT⟩ := hstabilization
  have hextension :=
    exists_supported_overlap_perfect_extension X W V hW hV T hT hTc (JW.obj R) hF hFT
  obtain ⟨Q, hQ, hQT, ⟨q⟩⟩ := hextension
  have hrestriction := exists_compact_overlap_restriction_model X W V hW hV
  obtain ⟨U, hU, hD, e, ⟨d⟩⟩ := hrestriction
  let := hD
  let : IsAffine V.toScheme := hV
  let L := (schemeOpenRestriction V.toScheme U).mapDerivedCategory
  let EV : schemeDerivedQCohCategory V.toScheme := ⟨JV.obj E.obj, by
    apply (schemeDerivedQCoh_openRestriction_iff X V E.obj).mpr
    intro n
    have := E.property n
    exact SheafOfModules.isQuasicoherent_over _ V⟩
  let α : SV.obj Q ⟶ SV.obj EV.obj :=
    q.hom ≫ SW.map a ≫ kW.hom.app E.obj ≫ kV.inv.app E.obj
  let α₀ : L.obj Q ⟶ L.obj EV.obj :=
    e.functor.preimage (d.hom.app Q ≫ α ≫ d.inv.app EV.obj)
  have hlift := exists_perfect_map_lift_of_isAffine V.toScheme U hU EV Q hQ α₀
  obtain ⟨B, I, δ, b, hB, _hI, _hδ, ⟨bU, _hbU, hα₀⟩, hBT⟩ := hlift
  let bS : SV.obj B ≅ SV.obj Q :=
    (d.app B).symm ≪≫ e.functor.mapIso bU ≪≫ d.app Q
  have hα : α = bS.inv ≫ SV.map b := by
    simpa only [bS, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
      using map_lift_transport L SV e d α bU b hα₀
  refine ⟨hA, hAT, B, b, q.symm ≪≫ bS.symm, hB, ?_, ?_⟩
  · exact hBT (Subtype.val ⁻¹' T) (hT.preimage continuous_subtype_val) hQT
  · change SW.map a ≫ kW.hom.app E.obj =
      (q.inv ≫ bS.inv) ≫ SV.map b ≫ kV.hom.app E.obj
    calc
      SW.map a ≫ kW.hom.app E.obj = q.inv ≫ α ≫ kV.hom.app E.obj := by
        dsimp only [α]
        simp only [Category.assoc, q.inv_hom_id_assoc, kV.inv_hom_id_app,
          Category.comp_id]
      _ = _ := by rw [hα]; simp only [Category.assoc]

end AlgebraicGeometry.Scheme
