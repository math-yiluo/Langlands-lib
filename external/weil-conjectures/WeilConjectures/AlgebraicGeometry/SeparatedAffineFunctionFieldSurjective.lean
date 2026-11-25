/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateModel
import WeilConjectures.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCore
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.RingTheory.LocalDomainDimOnePrincipalLocalization

/-!
# Separated affine and local charts surject onto the function field

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09NB,
proof, separatedness paragraph (blueprint: lem-sc-separated-affine-function-field-surjective)
-/

@[expose] public section

open scoped TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Source: Varieties Lemma 09NB, proof, separatedness paragraph
(blueprint: lem-sc-separated-affine-function-field-surjective).
The canonical tensor-product map from an affine open and a local stalk onto the
function field is surjective.

Proof (the three steps of the node):
1. The generic point lies in the nonempty open `U`. By
   `lem-sc-integral-scheme-stalks-in-function-field`, `B` is a domain inside `K`
   with fraction field `K`. The canonical map `Spec B → X` from
   `lem-weil-pbc-spec-local-ring-canonical-morphism` identifies its points with
   the generalizations of `x`. Since `B` is local of dimension one and `x ∉ U`,
   the inverse image of `U` consists only of the zero prime. Choose a nonzero
   element `f` of the maximal ideal of `B`. This inverse image is `D(f)`;
   `lem-weil-pbc-principal-localization-open-immersion` identifies it with `Spec B_f`.
   By `lem-weil-pbc-primes-of-localization`, `B_f` has only the zero prime, and
   `lem-sc-local-domain-dim-one-principal-localization-fraction-field` identifies
   `B_f` with `K`. Thus `lem-weil-pbc-open-immersion-base-change` gives
   `U ×_X Spec B = Spec K`. By `lem-weil-pbc-fibre-product-affine-spectra`,
   the ambient product over `Spec ℤ` is `Spec (A ⊗[ℤ] B)`, with the map
   induced by the two inclusions into `K`.
2. Separatedness (`def-weil-proper-morphism`) makes the diagonal of `X` a closed
   immersion. Base change along the product of `U → X` and `Spec B → X`, using
   `lem-weil-pbc-closed-immersion-base-change`, makes `Spec K` a closed subscheme
   of `Spec (A ⊗[ℤ] B)` under the identifications in step 1.
3. The affine criterion `lem-weil-pbc-closed-immersion-affine-cover-criterion` (1)
   says its map on global sections is surjective. This map is precisely the
   canonical tensor-product map induced by `A → K` and `B → K`. -/
theorem Scheme.separated_affine_functionField_surjective
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
    Function.Surjective φ := by
  dsimp only
  let f : TensorProduct ℤ (Γ(X, U)) (X.presheaf.stalk x) →ₐ[ℤ] X.functionField :=
    Algebra.TensorProduct.lift
      (X.germToFunctionField U).hom.toIntAlgHom
      (algebraMap (X.presheaf.stalk x) X.functionField).toIntAlgHom
      (fun _ _ => Commute.all _ _)
  change Function.Surjective f
  let hclosed := Scheme.isClosedImmersion_specMap_tensor_functionField X U hU x hx hdim
  exact @surjective_of_isClosedImmersion_SpecMap _ _ (CommRingCat.ofHom f.toRingHom) hclosed

end AlgebraicGeometry
