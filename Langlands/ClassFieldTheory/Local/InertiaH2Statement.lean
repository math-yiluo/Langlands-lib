import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.Cohomology.Continuous.FiniteQuotientSystem
import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.LocalField.Canonical

/-! # Vanishing of continuous degree-two cohomology of actual local inertia -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The actual inertia group has zero continuous degree-two cohomology with
the discrete algebraic-closure units and their restricted Galois action. -/
def InertiaH2Vanishing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    let I := F.absoluteInertia F.canonicalTopologicalData
    Subsingleton (continuousCohomology (k := IntegerScalars.{u}) 2
      (TopRep.res (Langlands.Continuous.subgroupInclusion I).toMonoidHom
        (absoluteUnits F.Carrier)))

end Langlands.ClassFieldTheory.Local
