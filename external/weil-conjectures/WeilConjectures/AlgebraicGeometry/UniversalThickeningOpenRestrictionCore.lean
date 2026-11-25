/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenPieces

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The open restriction data for a universal first order thickening exists.
Source: Stacks Project, More on Morphisms, Lemma 04FA and the general remarks in
Lemma 04F3 (blueprint: lem-weil-pbc-universal-thickening-open-restriction-core).
The proof restricts the closed immersion to the open determined by the image of
`V`, factors the structure maps through `U`, and applies the universal lifting
property; these constructions give the displayed equalities and universality. -/
theorem universalFirstOrderThickening_open_restriction_core
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : IsUniversalFirstOrderThickening h i h')
    (V : Z.Opens) (U : X.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    ∃ (hV : V.toScheme ⟶ U.toScheme),
      V.ι ≫ h = hV ≫ U.ι ∧ ∃ (V' : Z'.Opens) (iV : V.toScheme ⟶ V'.toScheme)
          (hV' : V'.toScheme ⟶ U.toScheme),
          i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
          iV ≫ V'.ι = V.ι ≫ i ∧ hV' ≫ U.ι = V'.ι ≫ h' ∧
          iV ≫ hV' = hV ∧ IsUniversalFirstOrderThickening hV iV hV' := by
  obtain ⟨V', hiV', hV'U, iV, hV, hV', hiV, hhV, hhV', HV⟩ :=
    (universalFirstOrderThickening_open_pieces h).2.1 i h' H V U hVU
  exact ⟨hV, hhV.symm, V', iV, hV', hiV', hV'U, hiV, hhV', HV.2.1, HV⟩

end AlgebraicGeometry
