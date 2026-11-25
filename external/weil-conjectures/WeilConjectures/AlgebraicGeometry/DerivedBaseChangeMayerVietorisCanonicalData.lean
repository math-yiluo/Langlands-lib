/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # SES boundaries and adjunction-compatible shifts for relative Mayer--Vietoris

Source: Stacks Project, Tags 08BV, 08HY and 0DJ9.
(blueprint: def-pc-rf-mv-canonical-ses-shifts).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The concrete open-image comparison, transported by the fixed resolution isomorphism.
Source: Stacks Tag 08BV (blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
def mvCanonicalOpenComparison (X : Scheme.{u}) (W : X.Opens)
    (K : schemeDerivedCategory X) :
    DerivedCategory.Q.obj (schemeOpenModuleImageComplex X W (schemeMVResolution X K)) ≅
      (schemeDerivedDirectImage W.ι).obj
        ((schemeOpenRestriction X W).mapDerivedCategory.obj K) :=
  schemeOpenModuleImageComplexComparison X W (schemeMVResolution X K)
      (mvOpenRestrictionAdjunction X W) ≪≫
    ((schemeOpenRestriction X W).mapDerivedCategory ⋙
      schemeDerivedDirectImage W.ι).mapIso (schemeMVResolutionIso X K)

/-- Boundary of the actual Mayer--Vietoris SES of the fixed K-injective resolution.
The comparisons are normalized to the pinned open adjunctions, not chosen from
existence of distinguished triangles. The equality hW merely transports the overlap.
Source: Stacks Tag 08BV (blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
def mvCanonicalBoundary (X : Scheme.{u}) (U V W : X.Opens)
    (hW : U ⊓ V = W) (hcover : U ⊔ V = ⊤) (K : schemeDerivedCategory X) :
    (schemeDerivedDirectImage W.ι).obj
      ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ⟶ K⟦(1 : ℤ)⟧ := by
  subst W
  exact (mvCanonicalOpenComparison X (U ⊓ V) K).inv ≫
    DerivedCategory.triangleOfSESδ
      (schemeMayerVietorisComplex_shortExact X U V hcover (schemeMVResolution X K)
        (fun _ ↦ inferInstance)) ≫ (schemeMVResolutionIso X K).hom⟦(1 : ℤ)⟧'

/-- Pullback shifts are the unique mates of the right-derived direct-image shifts
under exactly the adjunction used by the base-change map.
Source: Stacks Tags 079W and 08HY; Mathlib Shift.Adjunction.
(blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
@[instance_reducible] def mvCanonicalPullbackShift {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (derivedPullback g).CommShift ℤ :=
  (mvDerivedPullbackAdjunction g).leftAdjointCommShift ℤ

/-- The constructed shifts commute with both the pinned unit and counit.
Proof: Mathlib's mate construction satisfies Adjunction.CommShift by construction.
Source: Stacks Tag 079W (blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
theorem mvCanonicalPullbackShift_compatible {X Y : Scheme.{u}} (g : X ⟶ Y) :
    letI := mvCanonicalPullbackShift g
    (mvDerivedPullbackAdjunction g).CommShift ℤ :=
  (mvDerivedPullbackAdjunction g).commShift_of_rightAdjoint ℤ

/-- Transposition under the pinned adjunction respects the constructed shifts.
This is the specific equality used when transposing a connecting morphism.
Proof: expand homEquiv using the unit, apply shift_unit_app, and then use
naturality of the right adjoint's commutation isomorphism.
Source: Stacks Tags 079W and 08HY
(blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
theorem mvCanonicalHomEquiv_shift {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : schemeDerivedCategory Y) (K' : schemeDerivedCategory X)
    (ψ : (derivedPullback g).obj K ⟶ K') (n : ℤ) :
    letI := mvCanonicalPullbackShift g
    ((mvDerivedPullbackAdjunction g).homEquiv K K' ψ)⟦n⟧' =
      (mvDerivedPullbackAdjunction g).homEquiv (K⟦n⟧) (K'⟦n⟧)
        (((derivedPullback g).commShiftIso n).hom.app K ≫ ψ⟦n⟧') ≫
          ((schemeDerivedDirectImage g).commShiftIso n).hom.app K' := by
  let := mvCanonicalPullbackShift g
  let := mvCanonicalPullbackShift_compatible g
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [(mvDerivedPullbackAdjunction g).shift_unit_app]
  simp only [Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]

/-- With these compatible shifts pullback is triangulated, because its right
adjoint is the triangulated right-derived direct image.
Source: Stacks Tag 079W (blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
theorem mvCanonicalPullbackShift_triangulated {X Y : Scheme.{u}} (g : X ⟶ Y) :
    letI := mvCanonicalPullbackShift g
    (derivedPullback g).IsTriangulated := by
  let := mvCanonicalPullbackShift g
  let := mvCanonicalPullbackShift_compatible g
  exact (mvDerivedPullbackAdjunction g).isTriangulated_leftAdjoint

/-- Composite of the right-derived direct-image shift and its adjoint-compatible
pullback shift. Source: Stacks Tag 0DJ9
(blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
@[instance_reducible] def mvCanonicalSourceShift {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).CommShift ℤ :=
  letI := mvCanonicalPullbackShift g
  inferInstance

/-- The existing right-derived shift structure, with no independent choice.
Source: Stacks Tag 0DJ9 (blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
abbrev mvCanonicalTargetShift {X' S' : Scheme.{u}} (f' : X' ⟶ S') :
    (schemeDerivedDirectImage f').CommShift ℤ := inferInstance

end AlgebraicGeometry
