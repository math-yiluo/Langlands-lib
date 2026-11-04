import Langlands.AlgebraicGeometry.SchemeFiberGeometryLoci
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Local constructibility of the actual geometric-connectedness fibre locus -/

universe u

open Set Topology CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The geometric-component-count-one specialization of Stacks Lemma 37.28.6. -/
def GeometricallyConnectedFiberLocalConstructibility : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f],
      IsLocallyConstructible (geometricallyConnectedFiberLocus f)

/-- Local constructibility of the actual locus becomes constructibility on a
quasi-compact quasi-separated target. -/
theorem isConstructible_geometricallyConnectedFiberLocus_of_localConstructibility
    (h : GeometricallyConnectedFiberLocalConstructibility.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsConstructible (geometricallyConnectedFiberLocus f) :=
  (h f).isConstructible

/-- The exact combined fibre locus inherits local constructibility from its
two actual factors. -/
theorem isLocallyConstructible_nonemptyGeometricallyConnectedPureDimensionFiberLocus_of_factors
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (hc : IsLocallyConstructible (geometricallyConnectedFiberLocus f))
    (hd : IsLocallyConstructible (pureDimensionFiberLocus d f)) :
    IsLocallyConstructible
      (nonemptyGeometricallyConnectedPureDimensionFiberLocus d f) := by
  rw [nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq]
  exact hc.inter hd

/-- The corresponding global constructibility reduction needs no geometric
finiteness premise beyond the explicitly supplied factor conclusions. -/
theorem isConstructible_nonemptyGeometricallyConnectedPureDimensionFiberLocus_of_factors
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (hc : IsConstructible (geometricallyConnectedFiberLocus f))
    (hd : IsConstructible (pureDimensionFiberLocus d f)) :
    IsConstructible
      (nonemptyGeometricallyConnectedPureDimensionFiberLocus d f) := by
  rw [nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq]
  exact hc.inter hd

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
