/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Adjunction for the closed-site lift

## References

* Stacks Project, Tags 09BK and 097P
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The closed-site lift is left adjoint to base change, with invertible unit. -/
theorem exists_closedSiteAdjunction (A : Type u) [CommRing A] (I : Ideal A) :
    ∃ adj : closedSiteLift A I ⊣ closedSiteBaseChange A I, IsIso adj.unit := by
  obtain ⟨_, _, hfull, hfaithful, _, ⟨adj⟩, _, _⟩ :=
    affine_closed_site_functor_properties A I
  have : (closedSiteLift A I).Full := hfull
  have : (closedSiteLift A I).Faithful := hfaithful
  exact ⟨adj, adj.unit_isIso_of_L_fully_faithful⟩

end AlgebraicGeometry.Scheme.AffineProEt
