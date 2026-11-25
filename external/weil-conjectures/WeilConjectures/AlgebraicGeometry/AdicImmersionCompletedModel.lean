/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
public import WeilConjectures.AlgebraicGeometry.SfbCompletionNormalization

/-! # The fixed completed immersion pullback

Source: Stacks Tags 03A0, 03CY, 099L and 099R.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Algebraic inverse-image data for the specified transported geometric inverse image.
Its ring and module operations are fixed on generalized sections by InverseImageData.
Source: Stacks Tags 00YV and 03D2
(auxiliary; not a blueprint node). -/
def sfbImmersionAlgebra {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i] :
    ConstantCompletion.InverseImageData (SfbAdicRestriction.inverse i) :=
  Classical.choice (ConstantCompletion.inverseImageData_exists
    (SfbAdicRestriction.inverse i) (SfbAdicRestriction.direct i)
    (SfbAdicRestriction.adjunction i))

/-- The completed inverse image of the explicitly normalized localization representative.
Source: Bhatt--Scholze, Lemma 6.5.8
(auxiliary; not a blueprint node). -/
def sfbImmersionCompletedModel {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
    ConstantCompletion.D (ConstantCompletion.completed (proEtaleModelTopology S) A I) :=
  (SfbAdicRestriction.completedPull (sfbImmersionAlgebra i)
    (SfbAdicRestriction.direct i) (SfbAdicRestriction.adjunction i) A I).obj
      (SfbCompletionNormalization.object X I K)

end AlgebraicGeometry.Scheme
