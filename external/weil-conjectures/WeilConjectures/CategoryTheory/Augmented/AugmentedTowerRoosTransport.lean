/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData

import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Adjunction.Limits

set_option linter.privateModule false

/-! # Transport of strict augmented towers through the Roos construction

Source: Stacks Tag 08TC and the scalar-restriction paragraph of
`det-lem-int-tensor-pullback.proof.md`.
(blueprint: lem-sfb-augmented-tower-roos-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b c d
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
open CochainComplex CochainComplex.HomComplex WeilConjectures
section ProductRoos
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]
private def coconeCoordinates {K L : CochainComplex A ℤ} (φ : K ⟶ L) (i : ℤ) :
    (mappingCocone φ).X i ≅ K.X i ⊞ L.X (i - 1) where
  hom := biprod.lift ((mappingCocone.fst φ).f i)
    ((mappingCocone.snd φ).v i (i - 1) (by omega))
  inv := biprod.desc ((mappingCocone.inl φ).v i i (by omega))
    ((mappingCocone.inr φ).1.v (i - 1) i (by omega))
  hom_inv_id := by simpa using mappingCocone.id_X φ i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

end ProductRoos
attribute [local implicit_reducible] WeilConjectures.integralOperationsRoos
  WeilConjectures.integralOperationsRoosFunctor CochainComplex.mappingCocone

end CategoryTheory
