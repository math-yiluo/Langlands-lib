/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.AffineLocalFunctionFieldDiagonalPullback

@[expose] public section

open scoped TensorProduct
open AlgebraicGeometry

universe u
namespace AlgebraicGeometry

/-- The separated affine function-field construction yields a closed immersion of spectra.
Source: Varieties Lemma 09NB, separatedness paragraph
(blueprint: lem-sc-separated-affine-function-field-surjective-core).
The proof constructs the pullback of the diagonal along the affine charts, identifies it
with `Spec K`, and transports the resulting closed immersion through the affine-spectrum
identifications. -/
theorem Scheme.isClosedImmersion_specMap_tensor_functionField
    (X : Scheme.{u}) [IsIntegral X]
    [hsep : X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) [hUn : Nonempty U]
    (x : X) (hx : x ∉ U)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    let A : Type u := Γ(X, U)
    let B : Type u := X.presheaf.stalk x
    let K : Type u := X.functionField
    let φ : TensorProduct ℤ A B →ₐ[ℤ] K :=
      Algebra.TensorProduct.lift
        (X.germToFunctionField U).hom.toIntAlgHom
        (algebraMap B K).toIntAlgHom
        (fun _ _ => Commute.all _ _)
    IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
  dsimp only
  exact CategoryTheory.MorphismProperty.of_isPullback
    (Scheme.isPullback_affine_local_functionField_diagonal X U hU x hx hdim) inferInstance

end AlgebraicGeometry
