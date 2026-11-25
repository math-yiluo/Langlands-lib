/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.ProjectionFormulaCoproducts
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Right adjoint to proper étale derived direct image

Source: SGA 4, Exp. XVIII, Theorem 3.1.4; Stacks Project, Tag 0F5Y.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- For finite coefficients, proper étale derived direct image has a right adjoint.
Source: SGA 4, Exp. XVIII, Theorem 3.1.4; Stacks Project, Tag 0F5Y.
This is the finite-level step in the proof of `theorem-exceptional-inverse-image--15`
(auxiliary; not a blueprint node).

Proof in words: on each quasi-compact open of the base, a proper morphism is of
finite type and its geometric fibre dimensions have a common finite bound. The
proper base-change formula and the torsion cohomological dimension bound give
finite cohomological amplitude there. Higher direct images commute with filtered
colimits, hence with coproducts. The finite-amplitude argument then shows that
the unbounded derived direct image preserves coproducts on that open. Restriction
to such opens is exact, commutes with coproducts and detects isomorphisms, so the
coproduct comparison is an isomorphism globally. The source category of sheaves
of modules is Grothendieck abelian. Brown representability for its unbounded
derived category therefore gives a right adjoint to the exact,
coproduct-preserving derived direct image. -/
theorem isLeftAdjoint_proper_rightDerivedLowerStar
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] :
    (R((g)_*[ModuleCat.{u + 1} Λ])).IsLeftAdjoint := by
  -- Use the unbounded proper projection formula (Stacks 0F0G) to obtain
  -- coproduct preservation, then apply Grothendieck-derived Brown representability.
  let : Limits.HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    IsGrothendieckAbelian.hasColimits _
  let : Limits.HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    IsGrothendieckAbelian.hasColimits _
  let : Limits.HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    derived_hasCoproducts
  let : Limits.HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    derived_hasCoproducts
  apply grothendieckDerived_hasRightAdjoint
  intro I
  let := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).isLeftAdjoint
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ g
  apply preservesCoproducts_of_projectionFormula
    (L((g)^*[ModuleCat.{u + 1} Λ])) (R((g)_*[ModuleCat.{u + 1} Λ])) I
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g)
  change derivedTensorRightDerivedLowerStar (ModuleCat.{u + 1} Λ) g ≅
    rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar (ModuleCat.{u + 1} Λ) g
  exact asIso (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g)

end AlgebraicGeometry.Etale
