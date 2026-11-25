/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Bounded cohomology over a constant field has the same Tor bound

Source: Stacks Tags 03ER, 08FC, 08G0 and 08G1; Bhatt--Scholze Remark 6.3.2.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Over a constant field sheaf every module is flat, so a bounded object has the same
Tor interval. Source: Stacks Tags 03ER, 08FC, 08G0 and 08G1; Bhatt--Scholze Remark 6.3.2
(auxiliary; not a blueprint node).

Proof: use the homology bounds to put the derived object in the corresponding standard
truncation interval. Truncate a cochain representative at both ends to obtain a strict
bounded representative. Every term is flat by the constant-field flatness theorem, after
identifying the site tensor with the existing monoidal tensor. Apply the bounded-flat-model
criterion to this representative. The construction works for the zero object, an empty site,
and either sign of the interval endpoints. -/
theorem coefficientFieldTorBounds {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (k : Type w) [Field k]
    (K : ConstantCompletion.D (ConstantCompletion.constant J k))
    (a b : ℤ) (hab : a ≤ b)
    (h : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((coefficientModelCohomology _ q).obj K)) :
    HasCoefficientModelTorAmplitude _ K a b := by
  let R := ConstantCompletion.constant J k
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  have : K.IsGE a := (DerivedCategory.isGE_iff _ a).mpr
    (fun q hq ↦ h q (Or.inl hq))
  have : K.IsLE b := (DerivedCategory.isLE_iff _ b).mpr
    (fun q hq ↦ h q (Or.inr hq))
  obtain ⟨P, hPa, hPb, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE K a b
  apply (coefficientModelTorAmplitude_iff_flatModel R K a b hab).mpr
  refine ⟨P, hPa, hPb, fun i ↦ ?_, ⟨e.symm⟩⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X i))
    (SheafOfModules.isFlat_constantFieldModule J k (P.X i))

end CategoryTheory
