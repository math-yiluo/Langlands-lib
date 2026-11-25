/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryFinitePullExistence

/-! # Target projection model transport for ordinary finite reduction

The completed pullback followed by target projection is identified with the canonical
finite quotient model. This is the geometric part of the target transport.
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

/-- The target projection model is the canonical finite quotient pullback model.
Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL and 093M.
Proof: use the second-site quotient identification, the projection equation for
`completedMap`, and normalized scalar associativity for inverse-image pullback.
(auxiliary; not a blueprint node).
-/
theorem ordinaryReducedPull_targetProjectionIso
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((pull F (completedMap F A I) ⋙ change (projection J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1))))) := by
  have hp : completedMap F A I ≫ projection J' A I n =
      F.rings.map (projection J A I n) ≫
        constantMap F (A ⧸ I ^ (n + 1)) := by
    exact limit.lift_π _ (Opposite.op n)
  obtain ⟨d, _⟩ := finiteInverseScalar_exists J (F := F) V adj (projection J A I n)
  obtain ⟨s, _⟩ := finiteScalarComposite_exists J' (completedMap F A I)
    (projection J' A I n)
    (F.rings.map (projection J A I n) ≫ constantMap F (A ⧸ I ^ (n + 1))) hp
  obtain ⟨t, _⟩ := finiteScalarComposite_exists J' (F.rings.map (projection J A I n))
    (constantMap F (A ⧸ I ^ (n + 1))) _ rfl
  exact ⟨Functor.isoWhiskerLeft (F.algebra (completed J A I)).modules s ≪≫
    Functor.isoWhiskerLeft (F.algebra (completed J A I)).modules t.symm ≪≫
    Functor.isoWhiskerRight d (change (constantMap F (A ⧸ I ^ (n + 1))))⟩

end CategoryTheory.ConstantCompletion
