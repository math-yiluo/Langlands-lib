import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.KrullDimension.Zero

/-! # Scheme points and a closed subscheme with its open complement -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The support and factorization criteria for a closed subscheme and its open complement.
Local Artinian rings give coverage on underlying images and fields give coverage on
actual points. -/
def SchemePointStratificationStatement : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (X Z : Over (Spec (CommRingCat.of R))) (i : Z ⟶ X) [IsClosedImmersion i.left]
    (p : RingPoint R X S),
    let U := i.left.ker.support.compl
    let J := i.left.ker.comap p.left
    let supportedOnClosed := Set.range p.left ⊆ Set.range i.left
    let factorsThroughClosed := ∃ z : RingPoint R Z S, z ≫ i = p
    let factorsThroughOpen := ∃ q : RingPoint R (openOver R X U) S, openPointMap R X S U q = p
    (supportedOnClosed ↔ J ≤ (Spec (CommRingCat.of S)).nilradical) ∧
      (factorsThroughClosed ↔ J = ⊥) ∧
      (factorsThroughOpen ↔ Set.range p.left ⊆ (Set.range i.left)ᶜ) ∧
      (Nontrivial S → ¬(factorsThroughClosed ∧ factorsThroughOpen)) ∧
      (IsLocalRing S → IsArtinianRing S → supportedOnClosed ∨ factorsThroughOpen) ∧
      (IsField S → factorsThroughClosed ∨ factorsThroughOpen)

end Langlands.AlgebraicGeometry.PointTopology
