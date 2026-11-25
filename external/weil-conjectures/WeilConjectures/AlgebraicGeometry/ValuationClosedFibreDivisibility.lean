/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ValuationClosedFibreIntegral
import WeilConjectures.AlgebraicGeometry.ValuationClosedFibreSectionDivisible

/-! # Vanishing on the closed fibre implies divisibility

Source: Stacks Project, More on Morphisms, Tag 0EX8, general-case proof, second paragraph.
(blueprint: lem-sc-valuation-closed-fibre-divisibility)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- A section vanishing on the closed fibre is divisible by an element of the maximal ideal.

Source: Stacks Project, More on Morphisms, Tag 0EX8, proof of divisibility of the
chosen section, general valuation-ring case, second paragraph.
(blueprint: lem-sc-valuation-closed-fibre-divisibility)

Proof: The residue field of Spec A at its closed point is canonically A/m. The
pullback isomorphism therefore transports the integral quotient fibre to f.fiber
(closedPoint A), and transports the adjunction-unit restriction of sections.
If A is a field, vanishing on that fibre means s = 0; take π = 0 and t = 0.
Otherwise the closed-fibre section-vanishing lemma supplies nonzero π ∈ m such
that s vanishes on X times Spec(A/(π)). Because X/A is flat and L is locally free,
multiplication by π on L is injective. Locally, its cokernel is L/πL, identified
with the pushforward of the pullback to X times Spec(A/(π)); the quotient map is
the adjunction-unit restriction. Thus s lies in the kernel on global sections.
Left exactness of global sections gives a section t with π t = s. The local
lifts are unique by injectivity, so they glue. This step does not assume that s
is a basis, and uses no fraction field or generic triviality. -/
theorem closed_fibre_vanishing_is_divisible
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (hX₀ : IsIntegral (Limits.pullback f (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))))
    (s : Γ(L, ⊤)) :
    IsIntegral (f.fiber (IsLocalRing.closedPoint A)) ∧
      (((Classical.choose (exists_tensorPullbackAdjunction
        (f.fiberι (IsLocalRing.closedPoint A)))).unit.app L).val.app (op ⊤) s = 0 →
        ∃ π : A, π ∈ IsLocalRing.maximalIdeal A ∧ ∃ t : Γ(L, ⊤),
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π • t = s) := by
  refine ⟨closed_fibre_is_integral A X f hX₀, ?_⟩
  exact closed_fibre_section_is_divisible A X f L hX₀ s

end AlgebraicGeometry.Scheme.Modules
