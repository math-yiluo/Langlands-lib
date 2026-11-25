/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions



/-! # The single complex of coefficients restricted from W

Source: Stacks Project, Tags 03Q8 and 09Z1, cohomology of restricted coefficients.
(blueprint: def-sbc-higher-image-raw-over-complex).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The restricted coefficient sheaf placed in degree zero, shared by raw pullback
and its comparison. This is the actual single complex, with no choices added.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: def-sbc-higher-image-raw-over-complex). -/
noncomputable def higherDirectImageRawOverComplex
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (B : Over W) :
    DerivedCategory.Plus (Sheaf B.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)

/-- The shared complex is the original restricted single complex.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: def-sbc-higher-image-raw-over-complex).
Proof: Unfold the concrete construction; both sides are the same single complex. -/
theorem higherDirectImageRawOverComplex_eq
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (B : Over W) :
    higherDirectImageRawOverComplex Λ G B =
  (DerivedCategory.Plus.singleFunctor _ 0).obj (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G) := by rfl

end AlgebraicGeometry.Etale
