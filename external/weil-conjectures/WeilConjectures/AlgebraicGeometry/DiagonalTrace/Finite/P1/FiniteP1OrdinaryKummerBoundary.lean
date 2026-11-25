/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerCoordinates
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1OrdinaryKummerBoundaryCore

/-! # The integral boundary of the ordinary finite Kummer class

Source: diagonal-tower trace (1), the finite positive Kummer class and its site comparison.
(blueprint: lem-sfb-finite-p1-ordinary-kummer-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary positive Chern arrow, expressed in the finite coefficient coordinates,
has the integral positive Kummer boundary. No tower Chern construction occurs here.

Source: diagonal-tower trace (1), comparison with the scalar Kummer class;
Stacks 03PL and 03FD.
(blueprint: lem-sfb-finite-p1-ordinary-kummer-boundary).

Proof: the ordinary etale Chern arrow is characterized by its scalar Kummer
cohomology class. Pull it back along e. Naturality of the frame-torsor Picard
class and of the Kummer short exact sequence identifies its underlying class
with the Kummer boundary of e*O(1). Exact etale-to-pro-etale inverse image
preserves that connecting arrow. The units comparison sends a unit to the same
unit, and the Cartier roots comparison sends a root to the same root. The
section equations c.unit_sections and c.line_sections then identify respectively
the integral generator with finiteQuotient and the scalar root insertion with
finiteRootMap. Uniqueness on the constant generators and on pure root tensors
makes these comparisons equal as sheaf maps. Transport the derived arrows with
the exact single and shift comparisons used in finiteP1OrdinaryKummerArrow.
The inclusion_eq and power_eq of k identify its evaluated short exact sequence
with this Kummer sequence, so naturality of singleδ gives the displayed boundary
identity, with the positive sign. This proof contains no tower Chern arrow or
normalization hypothesis about such an arrow. Trivial Picard classes, empty
schemes, the zero coefficient ring and n=0 are covered by the same maps. -/
theorem finiteP1_ordinary_kummer_boundary
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (k : Kummer l X)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    FiniteKummerBoundary l E X n k
      (Scheme.Pic.mapHom e.hom (hyperplanePic S))
      (finiteP1OrdinaryKummerArrow l E n e hS c) := by
  apply finiteP1_ordinary_kummer_boundary_of_class l E e k hS n c
  exact (Etale.projectiveLineTraceDatum (l ^ (n + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (FiniteRing l E n)
    (ULift.ext (coefficient_annihilates l E n)) S
    (by simpa only [Nat.cast_pow] using hS.pow (n + 1))).chern_spec

end AlgebraicGeometry.ProEtale.DiagonalTrace
