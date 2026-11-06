import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.Smooth.Basic

/-! # Separation in every evaluation neighbourhood of a smooth domain -/

universe u v

open Filter Topology
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.RingTheory.LocalFieldDensity

/-- Local, rather than only global, separation by actual algebra points. -/
def LocalSeparationStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] [Algebra.Smooth K A] [IsDomain A]
    (x : AlgPoint K A K) (U : Set (AlgPoint K A K)), U ∈ 𝓝 x →
      ∀ a : A, a ≠ 0 → ∃ y ∈ U, y a ≠ 0

end Langlands.RingTheory.LocalFieldDensity
