/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.AlgebraicGeometry.EtaleGraphRefinementNormalization
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # The diagonal normalization of the specified product-graph map

Source: Stacks Project, Tags 0F7C--0F7E, and the repeated-presentation diagonal.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The graph map comparing a compactification with itself only inserts R(id)_*.
Source: Stacks Project, Tags 0F7C--0F7E, identity and proper diagonal pasting
(auxiliary; not a blueprint node).

Proof:
1. Use the existing compact-support formalism on the actual unbounded etale module-derived
   categories in UnboundedEtaleCompactSupportComparisons. Reuse its private refinement
   normalization through a proof-only import all, without introducing the public
   coherence theorem's Noetherian hypotheses or copying any declaration.
2. The unit equation for refinement open base change identifies the formalism's
   refinement comparison with the specified unit/inverse-base-change/K-injective-compositor
   word. This uses the mate Hom bijection and the derived conjugate compositor theorem.
3. Apply the formalism's proved identity-refinement law. Thus the specified refinement
   comparison for the identity refinement of c is the identity.
4. Apply the single-refinement graph normalization to that identity refinement, using
   the identity Cartesian square. Replace its refinement comparison by the identity.
   The result is exactly the inverse open normalization. -/
theorem etaleGraphComparison_diagonal
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    etaleGraphComparisonFromOpen A c (EtaleGraphPresentation.ofCompactification c) =
      (etaleGraphOpenNormalization A c).symm := by
  have hrho : rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) (Compactification.Refinement.id c)
      (IsPullback.id_vert c.i) = 𝟙 _ := by
    let := unbounded_has_base_change A
    rw [← unbounded_refinement_comparison A]
    exact (unboundedFormalism A).refinementComparison_eq_id _ _ rfl
  rw [etaleGraphFromOpen_refinement A c c (Compactification.Refinement.id c)
    (IsPullback.id_vert c.i)]
  have he : asIso (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) (Compactification.Refinement.id c)
      (IsPullback.id_vert c.i)) = Iso.refl _ :=
    Iso.ext hrho
  rw [he, Iso.refl_trans]

end AlgebraicGeometry.Etale
