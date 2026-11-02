import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Proper maps on actual points over locally compact fields -/

noncomputable section
universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (K : Type u) [Field K] [TopologicalSpace K]

/-- The local-field proper-map ingredient of Conrad Proposition 4.4. -/
def SchemePointLocalPropernessProperty
    [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
    (_hnondiscrete : ¬ DiscreteTopology K) : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left],
      letI : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
      letI : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
      IsProperMap (X := RingPoint K X K) (Y := RingPoint K Y K)
        (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K))

/-- Actual points of every proper scheme over a local field are compact. -/
def ProperSchemeLocalPointCompactnessProperty
    [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
    (_hnondiscrete : ¬ DiscreteTopology K) : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of K))) [IsProper X.hom],
    @CompactSpace (RingPoint K X K) (schemePointTopology K X K)

/-- Local properness and its absolute compactness consequence, for all local fields. -/
def LocalFieldProperPointProperties
    [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
    (hnondiscrete : ¬ DiscreteTopology K) : Prop :=
  SchemePointLocalPropernessProperty K hnondiscrete ∧
    ProperSchemeLocalPointCompactnessProperty K hnondiscrete

end Langlands.AlgebraicGeometry.PointTopology
