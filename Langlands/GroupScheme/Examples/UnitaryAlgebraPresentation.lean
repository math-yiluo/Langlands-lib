import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.GroupScheme.AffinePoints

/-! # Presentations of group schemes by special unitary points of an algebra with involution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnitaryAlgebra

open Langlands.CentralSimple.UnitaryPoints Langlands.GroupScheme.Quaternionic

variable {F : Type u} (E : Type u) {B : Type u} [Field F] [Field E] [Algebra F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

/-- A presentation of the group scheme `G` over `F` as the special unitary group `SU(B, τ)`:
on every commutative `F`-algebra `R` a group isomorphism from the `R`-points of `G` to the
special unitary points of `(B, τ)` with coefficients in `R`, natural in `R`. -/
structure Presentation (τ : FirstKindInvolution F B)
    (G : GroupScheme (Spec (CommRingCat.of F))) where
  /-- The group isomorphism on the points with coefficients in `R`. -/
  pointsEquiv : ∀ R : CommAlgCat.{u} (CommRingCat.of F),
    G.affinePoints R ≃* specialUnitaryPoints E τ R
  /-- Naturality in the coefficient algebra. -/
  naturality : ∀ {R S : CommAlgCat.{u} (CommRingCat.of F)} (f : R ⟶ S)
    (x : G.affinePoints R),
    pointsEquiv S (G.affinePointMap f x) = specialUnitaryMap E τ f.hom (pointsEquiv R x)

end Langlands.GroupScheme.UnitaryAlgebra
