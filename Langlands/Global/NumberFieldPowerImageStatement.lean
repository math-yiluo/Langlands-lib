import Langlands.Global.GlobalPlaceTopologyFacts
import Langlands.AlgebraicGeometry.PointTopology.AffineLinePuncturePow

/-! # Non-open images of power maps on number-field adelic units -/

noncomputable section

universe u

open CategoryTheory Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The image of the `n`th-power map is not open, both on the units of `S` with
Mathlib's units topology and on actual punctured-line points with values in `S`, for
every base ring. -/
def PowerImageNotOpen (S : Type u) [CommRing S] [TopologicalSpace S] (n : ℕ) : Prop :=
  ¬ IsOpen (Set.range (fun x : Sˣ => x ^ n)) ∧
    ∀ (R : Type u) [CommRing R] [Algebra R S],
      ¬ IsOpen (Set.range (α := RingPoint R (affineLinePuncture R) S)
        (fun p : RingPoint R (affineLinePuncture R) S => p ≫ affineLinePuncturePow R n))

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Conrad's example for a number field: every power map of exponent at least `2` has
non-open image on adelic units. -/
def NumberFieldPowerImageStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ), 2 ≤ n →
    PowerImageNotOpen (Adeles K) n

end Langlands.Global
