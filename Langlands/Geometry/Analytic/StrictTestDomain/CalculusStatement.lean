import Langlands.Geometry.Analytic.StrictTestDomain.Definitions
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Elementary calculus of representations with strict affinoid tests -/

universe u

namespace Langlands.Analytic.StrictTestDomain

/-- Identity, bounded-equivalence transport, unique comparison, and composition
over inverse images of closed subsets, for the strict-test representation
property. This does not assert that arbitrary pullbacks exist. -/
def CalculusStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    (∀ (P : PresentedStrictAffinoidAlgebra K),
      Represents K (BoundedAlgHom.id K P) Set.univ) ∧
    (∀ (P Q Q' : PresentedStrictAffinoidAlgebra K)
      (i : BoundedAlgHom K P Q) (e : BoundedAlgEquiv K Q Q')
      (U : Set (BanachSpectrum P)),
      Represents K (e.toBoundedAlgHom.comp i) U ↔ Represents K i U) ∧
    (∀ (P Q Q' : PresentedStrictAffinoidAlgebra K)
      (i : BoundedAlgHom K P Q) (i' : BoundedAlgHom K P Q')
      (U : Set (BanachSpectrum P)),
      Represents K i U → Represents K i' U →
      ∃! e : BoundedAlgEquiv K Q Q', e.toBoundedAlgHom.comp i = i') ∧
    (∀ (P Q R : PresentedStrictAffinoidAlgebra K)
      (i : BoundedAlgHom K P Q) (j : BoundedAlgHom K Q R)
      (U W : Set (BanachSpectrum P)),
      IsClosed W → Represents K i U →
      Represents K j (BanachSpectrum.comap i.toBoundedRingHom ⁻¹' W) →
      Represents K (j.comp i) (U ∩ W))

end Langlands.Analytic.StrictTestDomain
