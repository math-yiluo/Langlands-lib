/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BlowupChartStrictTransform

/-!
# The Rees model of the deformation space is the blow-up model, over affine opens

Let `I` be a quasi-coherent ideal on a scheme `X` and `U ⊆ X` an affine open. The chart of the
deformation space `D_I X = Spec_X 𝒪_X[t, I t⁻¹]` over `U` is `Spec Γ(U)[t, I(U) t⁻¹]`, and by
`AlgebraicGeometry.AffineBlowup.deformationChart` it is the complement of the strict transform
of `U × {0}` in the blow-up of `U × 𝔸¹ = Spec Γ(U)[t]` along `V(I(U)) × {0}`
(`AlgebraicGeometry.AffineBlowup.opensRange_deformationChart_eq_compl_strictTransform`). This
file records that this identification is compatible with the morphisms to the relative affine
line `Spec_X 𝒪_X[t]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

open AffineZariskiSite AffineBlowup

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.AffineZariskiSite)

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section,
comparison of the Rees model with the blow-up model over an affine open `U` of `X`. The chart of
`D_I X = Spec_X 𝒪_X[t, I t⁻¹]` over `U`, which is `Spec Γ(U)[t, I(U) t⁻¹]`, maps by the open
immersion `deformationChart` onto the complement of the strict transform of `U × {0}` in
`Bl_{V(I(U)) × 0} (Spec Γ(U)[t])`, and the blow-up map to `Spec Γ(U)[t] ⊆ Spec_X 𝒪_X[t]` is the
morphism `D_I X ⟶ Spec_X 𝒪_X[t]` given by `t`. -/
lemma deformationChart_toSpec_ι :
    deformationChart (I.siteIdeal U) ≫ toSpec (deformationCenter (I.siteIdeal U)) ≫
      colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U =
      colimit.ι (relativeGluingData I.coequifibered_toReesPresheaf).functor U ≫
        I.deformationSpaceToPolynomialSpec := by
  rw [deformationChart_toSpec_assoc, deformationSpaceToPolynomialSpec, ι_relativeGluingMap]
  rfl

end AlgebraicGeometry.Scheme.IdealSheafData
