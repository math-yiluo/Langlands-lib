import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Spreading geometric irreducibility from an actual generic fibre -/

universe u

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Stacks Lemma 37.27.5 (0559), with finite type written as local finite type
and quasi-compactness and with the generic point retained in the open set. -/
def FiniteTypeGeometricallyIrreducibleGenericSpreading : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y), IsGenericPoint η univ →
      GeometricallyIrreducible (f.fiberToSpecResidueField η) →
        ∃ V : Y.Opens, η ∈ V ∧ GeometricallyIrreducible (f ∣_ V)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
