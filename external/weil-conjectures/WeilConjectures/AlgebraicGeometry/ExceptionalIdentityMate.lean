/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-! Canonical exceptional tensor extraction and its projection/counit coherence. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
/--
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md
Step 4(iii): identity normalization of the specified exceptional and pullback comparisons
in the projection/counit tensor passage.

Proof:

For f=id_T, use the exact-derived pullback identity comparison and the proper forget-supports
comparison to identify the specified Rf_! with the identity functor. Under these comparisons the
projection map becomes the identity tensor map: this follows by expanding its exact-derived
definition and the unit and counit of the identity pullback/pushforward adjunction, whose
composites are identities.

The specified exceptional identity isomorphism is the right-adjoint uniqueness comparison for
that same lower-shriek identity comparison. Its counit equation therefore identifies the
exceptional counit with the identity counit after composing with that comparison. The exact-
derived pullback identity comparison is the second factor of the tensor map in the statement.

Transpose the identity-normalized inverse projection followed by the exceptional counit.
Naturality of the counit-preserving right-adjoint comparison gives tau_id(K,L) followed by c(K
tensor L) = c(K) tensor p(L), with c the specified exceptional identity and p the specified
pullback identity. This is the displayed equation. No invertibility of K or L and no alternative
choice of identity comparison enter this calculation.
(blueprint: lem-pur-exceptional-identity-mate)
-/
theorem exceptionalIdentityMate (T : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    lowerShriekRightAdjointTensorMap (rightDerivedUpperShriekAdjunction Λ (𝟙 T)) K L ≫
        (rightDerivedUpperShriekIdIso Λ T).hom.app
          (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj K).obj L) =
      derivedTensorHom (ModuleCat.{u + 1} Λ)
        ((rightDerivedUpperShriekIdIso Λ T).hom.app K)
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) T).hom.app L) := by
  sorry
end AlgebraicGeometry.Etale
