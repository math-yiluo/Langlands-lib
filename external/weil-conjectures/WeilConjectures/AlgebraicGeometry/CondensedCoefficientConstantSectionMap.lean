/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicEtale
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections

/-! Constant-section coefficient naturality for the finite condensed subfield inclusion.

Source: latest blueprint, lemma-fourier-transform-constant-sheaf proof, coefficient paragraph
(blueprint: lem-fd-unit-punctured-kernel-coefficient-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- The global constant section map commutes with the finite-subfield inclusion.

Proof in words. Apply the global-sections naturality theorem for a morphism of condensed
ring sheaves to the finite-subfield inclusion.  Both source and target families of constant
sections are natural by construction, and the component equality is the defining inclusion
`E → Q̄_ℓ`; the theorem then gives equality on global sections. -/
theorem condensed_constant_section_coefficient_map
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (t : E) :
    MonObj.Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E)
      (Profinite.continuousMapConstRingHom E t) =
        Profinite.PadicAlgCl.constRingHom ℓ (t : PadicAlgCl ℓ) := by
  exact Sheaf.Γ_map_ringHomΓSheafCompose _
    (Profinite.padicSubfieldCondensedRingToPadicAlgCl ℓ E) _
    (fun _ _ ↦ rfl) _ (fun _ _ ↦ rfl) (fun _ ↦ rfl)

end AlgebraicGeometry.ProEtale
