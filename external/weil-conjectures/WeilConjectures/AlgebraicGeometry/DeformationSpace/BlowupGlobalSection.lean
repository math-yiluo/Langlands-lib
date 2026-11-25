/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BlowupGlobalRange

/-!
# `g̃` and `s̃` in the blow-up model

For a morphism `g : V ⟶ B` with a section `s`, the deformation space `D_s V` of
`AlgebraicGeometry.Scheme.Hom.deformationSpaceProj` is the Rees model; by
`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceIsoBlowupModelOpen` it is an open
subscheme of `Bl_{s(B) × 0} (V ×_B 𝔸¹_B)`. Here we record that `g̃ : D_s V ⟶ 𝔸¹_B` is the
restriction of the blow-up map followed by `V ×_B 𝔸¹_B ⟶ 𝔸¹_B`, and that `s̃` lies over
`s × 𝔸¹` (blueprint `definition-deformation-normal-bundle`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {V B : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V)

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section. The map
`g̃ : D_s V ⟶ 𝔸¹_B` is the composite of the open immersion of `D_s V` into the blow-up
`Bl_{s(B) × 0} (V ×_B 𝔸¹_B)`, the blow-up map and `V ×_B 𝔸¹_B ⟶ 𝔸¹_B`. -/
lemma deformationSpaceProj_eq_blowup :
    deformationSpaceProj g s =
      s.ker.deformationSpaceToBlowup ≫ s.ker.deformationCenterSheaf.blowupMap ≫
        V.polynomialSpecToAffineSpace ≫ AffineSpace.map (ULift.{u} (Fin 1)) g := by
  rw [IdealSheafData.deformationSpaceToBlowup_blowupMap_assoc]
  rfl

/-- The section `s̃ : 𝔸¹_B ⟶ D_s V`, composed into the blow-up model, lies over
`s × 𝔸¹ : 𝔸¹_B ⟶ V ×_B 𝔸¹_B`. -/
lemma deformationSpaceSection_toBlowup_blowupMap :
    s.deformationSpaceSection ≫ s.ker.deformationSpaceToBlowup ≫
        s.ker.deformationCenterSheaf.blowupMap =
      AffineSpace.map (ULift.{u} (Fin 1)) s ≫ inv V.polynomialSpecToAffineSpace := by
  rw [IdealSheafData.deformationSpaceToBlowup_blowupMap, deformationSpaceSection_toPolynomialSpec]

end AlgebraicGeometry.Scheme.Hom
