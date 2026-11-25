/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionDerivedPull
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTargetIso
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTransportEquation

/-! # Ordinary finite transport for constant-completion pullback

Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL, 093M;
sites-cohomology.tex, Tag 06YY.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.ConstantCompletion

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

/-- Both finite reductions of the ordinary scalar comparison are transported to one
ordinary finite-module functor, and the comparison is the map induced by that transport.
The transport is assembled from the sectionwise quotient identifications, the normalized
finite pullback comparison, and the coefficient-map projection equation; on pure tensors
all three maps send `1 ⊗ m` to the same class.  This is the ordinary (underived) part of
the common-quotient insertion argument.
Proof: identify both finite-reduced sides with the same finite-module functor using the
sectionwise adic quotient and normalized pullback isomorphisms.  The projection equation
for the coefficient map makes these identifications natural, and the defining insertion
equation for `ordinaryPullComparison` gives the displayed equality.
Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL, 093M;
sites-cohomology.tex, Tag 06YY.
(auxiliary; not a blueprint node).
-/
theorem ordinaryReducedPull_transport
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ (X : Mod (completed J A I) ⥤ Mod (finite J' A I n))
      (s : (res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
        change (quotient J' A I n)) ≅ X)
      (t : (pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅ X),
      Functor.whiskerRight (ordinaryPullComparison F A I)
          (change (quotient J' A I n)) ≫ t.hom = s.hom := by
  let X := change (projection J A I n) ⋙
    pull F (constantMap F (A ⧸ I ^ (n + 1)))
  obtain ⟨s, t, h⟩ := ordinaryReducedPull_transport_eq F V adj A I n
  exact ⟨X, s, t, h⟩

end CategoryTheory.ConstantCompletion
