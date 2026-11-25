/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion
public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageRoosLimitData
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! Canonical derived-limit projection normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The canonical counit projections form the first map of the Milnor triangle.
Source: blueprint direct-image limits, proof (1); Stacks Tags 0940 and 0941.
(blueprint: lem-pbc-direct-image-roos-projection-data)

Proof: resolve a strict tower by a termwise injective K-injective tower I. Its
inverse limit is the kernel of the product difference 1-shift, and this difference
is degreewise surjective. The resulting short exact sequence gives a distinguished
triangle. Exact countable products identify its two product terms with products
of derived evaluations. The canonical derived adjunction counit on I is the image
of the ordinary constant-limit counit. Evaluating it and cancelling the canonical
constant-evaluation isomorphism identifies its nth component with the ordinary
limit projection. Thus the triangle's first map is Pi.lift of levelProjection.
Naturality of the derived comparison and counit transports the triangle along
the resolution isomorphism to every derived tower. -/
theorem directImage_roos_projection_data (T : Scheme.{u}) :
    ∃ (_ : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E T))),
      ∀ M : DTow l E T,
        ∃ δ, IsDerivedLimitTriangle (fun n : ℕ ↦ (transition l E T n).app M) _
          (Pi.lift fun n : ℕ ↦ (levelProjection l E T n).app M) δ := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
