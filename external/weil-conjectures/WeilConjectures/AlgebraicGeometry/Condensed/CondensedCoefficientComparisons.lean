/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Canonical derived condensed coefficient comparisons

Source: master ModuleObject/Colimit/TwoColimit.lean, ExtendScalars;
ModuleObjects/ExtendScalars.lean, Compatibilities
(blueprint: def-weil-pbc-condensed-coefficient-comparisons).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

variable (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Composition of finite coefficient inclusions.
Source: Compatibility.lean, RingObj
(blueprint: def-weil-pbc-condensed-coefficient-comparisons).
Proof: the inclusions of continuous functions compose pointwise, by
`Profinite.padicSubfieldRingObjMap_comp`. Apply `coefficientMap_comp`, since
`coefficientMap` is the functor `upperStarFromPoint T` on morphisms. -/
theorem condensedCoefficientMap_comp
    {E F G : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)}
    (h : E ≤ F) (k : F ≤ G) :
    padicSubfieldRingObjMap T ℓ h ≫ padicSubfieldRingObjMap T ℓ k =
      padicSubfieldRingObjMap T ℓ (h.trans k) := by
  rw [← coefficientMap_comp, ← Profinite.padicSubfieldRingObjMap_comp]

/-- Identity coefficient inclusion.
Source: Compatibility.lean, RingObj
(blueprint: def-weil-pbc-condensed-coefficient-comparisons).
Proof: `Profinite.padicSubfieldRingObjMap_id` identifies the inclusion with the
identity on the point, and `coefficientMap_id` preserves that identity. -/
theorem condensedCoefficientMap_id
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    padicSubfieldRingObjMap T ℓ (le_refl E) = 𝟙 _ := by
  change coefficientMap (Profinite.padicSubfieldRingObjMap ℓ (le_refl E)) T = _
  rw [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id]

/-- Exactness of the composite finite coefficient extension.
Source: TwoColimit.lean, ExtendScalars
(blueprint: def-weil-pbc-condensed-coefficient-comparisons).
Proof: composition identifies this ring map with the direct coefficient inclusion.
Transport its exactness through `Mod.extendScalarsIsoOfEq`; the direct inclusion is
exact by Compatibility.lean, Flat. This fixes only a proof, not any comparison data. -/
theorem condensedCoefficientCompositeExact
    {E F G : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)}
    (h : E ≤ F) (k : F ≤ G) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h ≫
        padicSubfieldRingObjMap T ℓ k)) := by
  exact preservesFiniteLimits_of_natIso
    (Mod.extendScalarsIsoOfEq (condensedCoefficientMap_comp T ℓ h k)).symm

attribute [instance] condensedCoefficientCompositeExact

/-- The canonical derived multiplication comparison for three finite coefficient fields.
Source: TwoColimit.lean, ExtendScalars; ExtendScalars.lean, `extendScalarsComp`
(blueprint: def-weil-pbc-condensed-coefficient-comparisons).
The underlying comparison is the inverse of `Mod.extendScalarsComp`, followed by
transport along composition of the inclusions. Thus it is induced by
`c ⊗ (b ⊗ p) ↦ cb ⊗ p`, with inverse `c ⊗ p ↦ c ⊗ (1 ⊗ p)`.
Exactness allows total left derivation of this underived natural isomorphism. -/
noncomputable def condensedCoefficientCompIso
    {E F G : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)}
    (h : E ≤ F) (k : F ≤ G) :
    derivedExtendScalarsSubfield T ℓ h ⋙ derivedExtendScalarsSubfield T ℓ k ≅
      derivedExtendScalarsSubfield T ℓ (h.trans k) :=
  (Functor.leftDerivedFunctorCompIso _ _).symm ≪≫
    Functor.leftDerivedFunctorNatIso _
      ((Mod.extendScalarsComp _ _).symm ≪≫
        Mod.extendScalarsIsoOfEq (condensedCoefficientMap_comp T ℓ h k))

/-- Canonical derived scalar unit comparison, induced by `a ⊗ p ↦ ap`.
Source: ExtendScalars.lean, `extendScalarsId`; exact-functor identity comparison
(blueprint: def-weil-pbc-condensed-coefficient-comparisons). -/
noncomputable def condensedCoefficientUnitIso
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    derivedExtendScalarsSubfield T ℓ (le_refl E) ≅
      𝟭 (DerivedCategory
        (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E))) :=
  Functor.leftDerivedFunctorNatIso _
      (Mod.extendScalarsIsoOfEq (condensedCoefficientMap_id T ℓ E) ≪≫
        Mod.extendScalarsId) ≪≫
    (𝟭 (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (padicSubfieldRingObj T ℓ E))).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The canonical shifts of finite coefficient extension, transported from termwise tensor.
Source: ExactFunctor.lean, exact-functor shifts
(blueprint: def-weil-pbc-condensed-coefficient-comparisons). -/
noncomputable instance condensedCoefficientCommShift
    {E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)} (h : E ≤ F) :
    (derivedExtendScalarsSubfield T ℓ h).CommShift ℤ :=
  Functor.CommShift.ofIso
    ((Mod.extendScalars
      (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctorIsoMapDerivedCategory.symm) ℤ

/-- The canonical shifts of extension to the closure, transported from termwise tensor.
Source: ExactFunctor.lean, exact-functor shifts
(blueprint: def-weil-pbc-condensed-coefficient-comparisons). -/
noncomputable instance condensedAlgClCoefficientCommShift
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    (derivedExtendScalarsToPadicAlgCl T ℓ E).CommShift ℤ :=
  Functor.CommShift.ofIso
    ((Mod.extendScalars
      (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctorIsoMapDerivedCategory.symm) ℤ

end AlgebraicGeometry.ProEtale
