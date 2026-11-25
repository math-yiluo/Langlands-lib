/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! Exact structures required by the two generation arguments. Choose the
already proved exact shift of derivedPullback, the canonical exact tensor
shifts, and the right-adjoint shifts from Mathlib. No compatibility with a
supplied monoidal tensorator or comparison transformation is asserted.
Source: derived-pullback existence (Stacks Tag 06YJ), canonical tensor exactness
(Tag 06YH), and Mathlib.CategoryTheory.Triangulated.Adjunction.
(blueprint: lem-sc-derived-separate-exact-structures). -/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.ShiftSaturated
open AlgebraicGeometry

/-- The supported quasi-coherent triangulated property at the whole space is D_QCoh.
Source: Stacks Tag 0A9A. Proof: identify the two object properties by extensionality
and apply supported_qcoh_isTriangulated at Set.univ.
(blueprint: lem-sc-derived-separate-exact-structures). -/
theorem qc_triangulated (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    (schemeDerivedQCohProperty X).IsTriangulated := by
  have he : supportedProperty X Set.univ = schemeDerivedQCohProperty X := by
    ext K
    simp [supportedProperty]
  rw [← he]
  exact supported_qcoh_isTriangulated X Set.univ

/-- Separate exact shifts for the pullback-tensor lift and the specified right adjoint.
Source: Stacks Tags 06YJ and 06YH; Mathlib Triangulated.Adjunction.
Proof: use the exact shift from derivedPullback_spec; transfer it to direct image
by its adjunction. TensorRight is exact for the canonical tensor shift. Lift exactness
through the quasi-coherent inclusions and use the restricted adjunction for c.
(blueprint: lem-sc-derived-separate-exact-structures). -/
theorem rightAdjointTensor_exactStructures
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [(schemeDerivedQCohProperty Y).IsTriangulated]
    [(schemeDerivedQCohProperty Z).IsTriangulated]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c) :
    let Q := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
    ∃ (sQ : Q.CommShift ℤ) (sC : c.CommShift ℤ),
      letI := sQ
      letI := sC
      Q.IsTriangulated ∧ c.IsTriangulated := by
  let := qc_triangulated Y
  let := qc_triangulated Z
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨sL, hL⟩, _⟩ :=
    derivedPullback_spec f
  let : (derivedPullback f).CommShift ℤ := sL
  let : (derivedPullback f).IsTriangulated := hL
  let := a.rightAdjointCommShift ℤ
  let := a.commShift_of_leftAdjoint ℤ
  let : (schemeDerivedDirectImage f).IsTriangulated := a.isTriangulated_rightAdjoint
  let := schemeCanonicalTensorShift Z
  let : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  let : ∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated :=
    (schemeCanonicalTensorShift_properties Z).1
  let R := (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf
  let : R.CommShift ℤ := inferInstance
  let : R.IsTriangulated := inferInstance
  let := adj.rightAdjointCommShift ℤ
  let := adj.commShift_of_leftAdjoint ℤ
  let : c.IsTriangulated := adj.isTriangulated_rightAdjoint
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Separate exact shifts for the two functors in the projection comparison.
Source: Stacks Tags 06YJ and 06YH; Mathlib Triangulated.Adjunction.
Proof: take the already exact pullback shift, the canonical tensor shifts on Y and Z,
and the right-adjoint shift on direct image. Composition and the full-subcategory
inclusion give the two displayed exact functors.
(blueprint: lem-sc-derived-separate-exact-structures). -/
theorem projection_exactStructures
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [(schemeDerivedQCohProperty Y).IsTriangulated]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (E : schemeDerivedCategory Z) :
    let F := (schemeDerivedQCohProperty Y).ι ⋙
      tensorRight ((schemeDerivedDirectImage f).obj E)
    let G := (schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
      tensorRight E ⋙ schemeDerivedDirectImage f
    ∃ (sF : F.CommShift ℤ) (sG : G.CommShift ℤ),
      letI := sF
      letI := sG
      F.IsTriangulated ∧ G.IsTriangulated := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨sL, hL⟩, _⟩ :=
    derivedPullback_spec f
  let : (derivedPullback f).CommShift ℤ := sL
  let : (derivedPullback f).IsTriangulated := hL
  let := a.rightAdjointCommShift ℤ
  let := a.commShift_of_leftAdjoint ℤ
  let : (schemeDerivedDirectImage f).IsTriangulated := a.isTriangulated_rightAdjoint
  let := schemeCanonicalTensorShift Y
  let := schemeCanonicalTensorShift Z
  let : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  let : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  let : ∀ M : schemeDerivedCategory Y, (tensorRight M).IsTriangulated :=
    (schemeCanonicalTensorShift_properties Y).1
  let : ∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated :=
    (schemeCanonicalTensorShift_properties Z).1
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end CategoryTheory.ShiftSaturated
