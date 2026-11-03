import Langlands.AlgebraicGeometry.PointTopology.AffineLinePuncture

/-!
# The affine-line correction to Conrad's Remark 3.3
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped DualNumber

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Underlying-image containment is nilpotence, whereas actual factorization
through the origin is the zero-coordinate condition. -/
def AffineLineStratificationProperties : Prop :=
  let Z : Set (RingPoint R (ringTest R (MvPolynomial Unit R)) S) :=
    Set.range (fun p : RingPoint R (ringTest R R) S => p ≫ affineLineOrigin R)
  let U : Set (RingPoint R (ringTest R (MvPolynomial Unit R)) S) :=
    Set.range (fun p : RingPoint R (affineLinePuncture R) S =>
      p ≫ affineLinePunctureι R)
  ((affineLinePuncturedOpen R : Set (ringTest R (MvPolynomial Unit R)).left) =
    (Set.range (affineLineOrigin R).left)ᶜ) ∧
  (∀ p : RingPoint R (ringTest R (MvPolynomial Unit R)) S,
    Set.range p.left ⊆ Set.range (affineLineOrigin R).left ↔
      IsNilpotent (affineLinePointEquiv R S p)) ∧
  (∀ p, p ∈ Z ↔ affineLinePointEquiv R S p = 0) ∧
  (∀ p, p ∈ U ↔ IsUnit (affineLinePointEquiv R S p)) ∧
  (Nontrivial S → Disjoint Z U) ∧
  (Z ∪ U = Set.univ ↔ ∀ s : S, s = 0 ∨ IsUnit s)

/-- Source-qualified correction: the field coverage survives, and the
local Artinian coverage assertion fails for an actual epsilon point. -/
def ConradRemark33Correction : Prop :=
  (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    AffineLineStratificationProperties R S) ∧
  (∀ (R K : Type u) [CommRing R] [Field K] [Algebra R K],
    Set.range (fun p : RingPoint R (ringTest R R) K => p ≫ affineLineOrigin R) ∪
      Set.range (fun p : RingPoint R (affineLinePuncture R) K =>
        p ≫ affineLinePunctureι R) = Set.univ) ∧
  (∀ (K : Type u) [Field K],
    let p := (affineLinePointEquiv K[ε] K[ε]).symm (ε : K[ε])
    IsLocalRing K[ε] ∧ IsArtinianRing K[ε] ∧ IsNilpotent (ε : K[ε]) ∧
      (Set.range p.left ⊆ Set.range (affineLineOrigin K[ε]).left) ∧
      p ∉ Set.range (fun q : RingPoint K[ε] (ringTest K[ε] K[ε]) K[ε] =>
        q ≫ affineLineOrigin K[ε]) ∧
      p ∉ Set.range (fun q : RingPoint K[ε] (affineLinePuncture K[ε]) K[ε] =>
        q ≫ affineLinePunctureι K[ε]))

end Langlands.AlgebraicGeometry.PointTopology
